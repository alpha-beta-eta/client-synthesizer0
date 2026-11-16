//! Function index of Rust / Verus source files, from the Verus fork of syn.
//!
//! Usage: item-index <file.rs>...
//! For every function (free, in an impl block, or declared in a trait),
//! including those inside `verus! { ... }`, prints
//!
//!   (item (file "...") (name "f") (start L) (end L)
//!         (self "Type" | #f) (trait "Trait" | #f) (in-trait "Trait" | #f)
//!         (module "a::b" | "")
//!         (muts ("x" #t | #f) ...))
//!
//! `self` and `trait` are the impl block's self type and implemented trait,
//! as written in the source; `in-trait` is set for trait method
//! declarations; `module` is the path of inline `mod` blocks in the file.
//!
//! `muts` lists the `&mut` parameters, including those in a `#[verus_spec]`
//! `with` clause, and says whether the borrow can flow into the return value
//! (including ghost return values).  By the borrow rules it can only if the
//! lifetime of the parameter's reference occurs in the return type: a named
//! lifetime `'a` occurs literally (or through `Self`, when the impl's self
//! type mentions `'a`); an elided one occurs when the return type has an
//! elided lifetime (`&T`, `'_`, or a type defined with lifetime parameters
//! written without them) and Rust's elision rules bind it to this parameter.
//! Types defined with lifetime parameters are collected from all the files
//! given on the command line.

use quote::ToTokens;
use std::collections::{BTreeSet, HashMap};
use verus_syn::{
    spanned::Spanned, FnArg, FnArgKind, GenericArgument, ImplItem, Item, Pat, PathArguments,
    ReturnType, Signature, TraitItem, Type, TypeParamBound,
};

mod full;

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    // `--expr`: the tree of one expression read from stdin (full.rs)
    if args.first().map(|a| a.as_str()) == Some("--expr") {
        let mut input = String::new();
        std::io::Read::read_to_string(&mut std::io::stdin(), &mut input).expect("stdin");
        match full::parse_expr(&input) {
            Ok(t) => println!("{t}"),
            Err(e) => { println!("(error {})", s(&e)); std::process::exit(1) }
        }
        return;
    }
    // `--exprs`: one expression per line of stdin, one tree (or `(error ..)`) per line
    if args.first().map(|a| a.as_str()) == Some("--exprs") {
        let mut input = String::new();
        std::io::Read::read_to_string(&mut std::io::stdin(), &mut input).expect("stdin");
        for line in input.lines() {
            match full::parse_expr(line) {
                Ok(t) => println!("{t}"),
                Err(e) => println!("(error {})", s(&e)),
            }
        }
        return;
    }
    // `--full`: signatures, clauses, datatypes (full.rs); otherwise the item index
    // `--full-spans`: as --full, every node of the trees wrapped (@ "SPAN" NODE)
    // (docs/representation.md 10.4, step 1: aligning the source's trees with VIR's)
    let spans_mode = args.first().map(|a| a.as_str()) == Some("--full-spans");
    if spans_mode { full::NODE_SPANS.store(true, std::sync::atomic::Ordering::Relaxed); }
    let full_mode = spans_mode || args.first().map(|a| a.as_str()) == Some("--full");
    if full_mode { args.remove(0); }
    let files: Vec<(String, String, verus_syn::File)> = args.into_iter()
        .filter_map(|path| {
            let src = std::fs::read_to_string(&path).ok()?;
            match verus_syn::parse_file(&src) {
                Ok(f) => Some((path, src, f)),
                Err(e) => { eprintln!("{path}: parse error: {e}"); None }
            }
        })
        .collect();
    let mut cx = Cx { lifetime_types: HashMap::new(), out: String::new(), rejoin: full_mode };
    let rejoin = cx.rejoin;
    for (path, _, f) in &files { collect_types(path, &f.items, &mut cx.lifetime_types, rejoin); }
    if full_mode {
        for (path, src, f) in &files {
            let src = full::Src::new(path, src);
            full::walk_full(&src, "", &f.items, &mut cx, &mut HashMap::new());
        }
    } else {
        for (path, _, f) in &files { walk(path, "", &f.items, &mut cx); }
    }
    print!("{}", cx.out);
}

struct Cx {
    /// type name -> number of lifetime parameters in its definition
    lifetime_types: HashMap<String, usize>,
    /// rejoin the tokens of `verus! { }` as Verus does (`!is`, `!has`) before parsing
    /// them; only with --full, so that the item index stays as it was
    rejoin: bool,
    out: String,
}

fn s(t: &str) -> String {
    let mut r = String::from("\"");
    for c in t.chars() {
        match c { '"' => r.push_str("\\\""), '\\' => r.push_str("\\\\"), '\n' | '\r' => r.push(' '), c => r.push(c) }
    }
    r.push('"');
    r
}

/// Token text with the spaces `to_string` puts around punctuation removed.
fn text<T: ToTokens>(t: &T) -> String {
    let raw = t.to_token_stream().to_string();
    let mut r = raw.replace(" < ", "<").replace("< ", "<").replace(" >", ">").replace(" ,", ",")
        .replace(" :: ", "::").replace(":: ", "::").replace(" ::", "::").replace("& ", "&")
        .replace("' ", "'").replace(" (", "(").replace("( ", "(").replace(" )", ")");
    while r.contains("  ") { r = r.replace("  ", " "); }
    r
}

fn opt(o: &Option<String>) -> String {
    match o { Some(t) => s(t), None => "#f".into() }
}

// ================================================================ lifetimes

/// Lifetimes occurring in a type.
#[derive(Default)]
struct Lts {
    named: BTreeSet<String>,
    elided: bool,
    has_self: bool,
}

impl Lts {
    fn lifetime(&mut self, l: &verus_syn::Lifetime) {
        match l.ident.to_string().as_str() {
            "_" => self.elided = true,
            "static" => {}
            n => { self.named.insert(n.to_string()); }
        }
    }
}

fn collect_types(path: &str, items: &[Item], acc: &mut HashMap<String, usize>, rejoin: bool) {
    for item in items {
        let (name, g) = match item {
            Item::Struct(x) => (x.ident.to_string(), &x.generics),
            Item::Enum(x) => (x.ident.to_string(), &x.generics),
            Item::Union(x) => (x.ident.to_string(), &x.generics),
            Item::Type(x) => (x.ident.to_string(), &x.generics),
            Item::Mod(m) => { if let Some((_, inner)) = &m.content { collect_types(path, inner, acc, rejoin); } continue }
            Item::Macro(m) if is_verus(m) => {
                if let Ok(f) = verus_syn::parse2::<verus_syn::File>(macro_tokens(m, rejoin)) { collect_types(path, &f.items, acc, rejoin); }
                continue
            }
            _ => continue,
        };
        let n = g.lifetimes().count();
        if n > 0 { acc.insert(name, n); }
    }
}

fn type_lts(t: &Type, cx: &Cx, acc: &mut Lts) {
    match t {
        Type::Reference(r) => {
            match &r.lifetime { Some(l) => acc.lifetime(l), None => acc.elided = true }
            type_lts(&r.elem, cx, acc);
        }
        Type::Path(p) => {
            if let Some(q) = &p.qself { type_lts(&q.ty, cx, acc); }
            if p.path.segments.len() == 1 && p.path.segments[0].ident == "Self" { acc.has_self = true; }
            for (i, seg) in p.path.segments.iter().enumerate() {
                let mut lifetime_args = 0;
                if let PathArguments::AngleBracketed(a) = &seg.arguments {
                    for arg in &a.args {
                        match arg {
                            GenericArgument::Lifetime(l) => { lifetime_args += 1; acc.lifetime(l) }
                            GenericArgument::Type(t) => type_lts(t, cx, acc),
                            GenericArgument::AssocType(b) => type_lts(&b.ty, cx, acc),
                            _ => {}
                        }
                    }
                }
                // `CursorMut<M>` for `struct CursorMut<'a, M>`: the lifetime is elided
                if i + 1 == p.path.segments.len() && lifetime_args == 0
                    && cx.lifetime_types.get(&seg.ident.to_string()).map_or(false, |n| *n > 0) {
                    acc.elided = true;
                }
            }
        }
        Type::Tuple(x) => for e in &x.elems { type_lts(e, cx, acc) },
        Type::Array(x) => type_lts(&x.elem, cx, acc),
        Type::Slice(x) => type_lts(&x.elem, cx, acc),
        Type::Paren(x) => type_lts(&x.elem, cx, acc),
        Type::Group(x) => type_lts(&x.elem, cx, acc),
        Type::Ptr(x) => type_lts(&x.elem, cx, acc),
        Type::ImplTrait(x) => bounds_lts(x.bounds.iter(), cx, acc),
        Type::TraitObject(x) => bounds_lts(x.bounds.iter(), cx, acc),
        _ => {}
    }
}

fn bounds_lts<'b>(bs: impl Iterator<Item = &'b TypeParamBound>, cx: &Cx, acc: &mut Lts) {
    for b in bs {
        match b {
            TypeParamBound::Lifetime(l) => acc.lifetime(l),
            TypeParamBound::Trait(t) => {
                for seg in &t.path.segments {
                    if let PathArguments::AngleBracketed(a) = &seg.arguments {
                        for arg in &a.args {
                            match arg {
                                GenericArgument::Lifetime(l) => acc.lifetime(l),
                                GenericArgument::Type(t) => type_lts(t, cx, acc),
                                GenericArgument::AssocType(b) => type_lts(&b.ty, cx, acc),
                                _ => {}
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// The lifetime of a parameter's outermost reference.
#[derive(Clone, PartialEq)]
enum RefLt { Named(String), Elided }

/// A parameter: its name, its outermost reference (if any), whether that
/// reference is `&mut`, and the number of lifetime positions it has.
struct Param { name: String, refl: Option<(RefLt, bool)>, receiver: bool, lts: Lts }

/// The outermost reference of a parameter type, looking through `Tracked<..>`
/// and `Ghost<..>`.
fn outer_ref(t: &Type) -> Option<(RefLt, bool)> {
    match t {
        Type::Reference(r) => {
            let l = match &r.lifetime {
                Some(l) if l.ident != "_" => RefLt::Named(l.ident.to_string()),
                _ => RefLt::Elided,
            };
            Some((l, r.mutability.is_some()))
        }
        Type::Paren(x) => outer_ref(&x.elem),
        Type::Group(x) => outer_ref(&x.elem),
        Type::Path(p) => {
            let seg = p.path.segments.last()?;
            if seg.ident != "Tracked" && seg.ident != "Ghost" { return None }
            if let PathArguments::AngleBracketed(a) = &seg.arguments {
                if let Some(GenericArgument::Type(t)) = a.args.first() { return outer_ref(t) }
            }
            None
        }
        _ => None,
    }
}

/// The variable a parameter pattern binds: `x`, `mut x`, `Tracked(x)`.
fn pat_name(p: &Pat) -> Option<String> {
    match p {
        Pat::Ident(i) => Some(i.ident.to_string()),
        Pat::TupleStruct(t) => t.elems.first().and_then(pat_name),
        Pat::Tuple(t) => t.elems.first().and_then(pat_name),
        Pat::Paren(x) => pat_name(&x.pat),
        Pat::Reference(x) => pat_name(&x.pat),
        Pat::Type(x) => pat_name(&x.pat),
        _ => None,
    }
}

fn param(a: &FnArg, cx: &Cx) -> Option<Param> {
    match &a.kind {
        FnArgKind::Receiver(r) => {
            let mut lts = Lts::default();
            type_lts(&r.ty, cx, &mut lts);
            Some(Param { name: "self".into(), refl: outer_ref(&r.ty), receiver: true, lts })
        }
        FnArgKind::Typed(pt) => {
            let mut lts = Lts::default();
            type_lts(&pt.ty, cx, &mut lts);
            Some(Param { name: pat_name(&pt.pat)?, refl: outer_ref(&pt.ty), receiver: false, lts })
        }
    }
}

/// The `#[verus_spec(...)]` attribute of a function, parsed.
fn verus_spec_attr(attrs: &[verus_syn::Attribute]) -> Option<verus_syn::SignatureSpecAttr> {
    let a = attrs.iter().find(|a| a.path().segments.last().map_or(false, |s| s.ident == "verus_spec"))?;
    match &a.meta {
        verus_syn::Meta::List(l) => verus_syn::parse2::<verus_syn::SignatureSpecAttr>(l.tokens.clone()).ok(),
        _ => None,
    }
}

/// `muts` for one function: (name, borrow may flow into the return value).
fn mut_flows(sig: &Signature, attrs: &[verus_syn::Attribute], impl_self: Option<&Type>, cx: &Cx) -> Vec<(String, bool)> {
    ref_flows(sig, attrs, impl_self, cx, false).into_iter().map(|(n, _, f)| (n, f)).collect()
}

/// Every reference parameter (shared too, with all_refs): (name, is_mut, may flow into the result).
pub(crate) fn ref_flows(sig: &Signature, attrs: &[verus_syn::Attribute], impl_self: Option<&Type>, cx: &Cx, all_refs: bool) -> Vec<(String, bool, bool)> {
    // parameters: the signature's, then the `with` clause's (from the
    // signature in `verus!` syntax, or from the `#[verus_spec]` attribute)
    let attr = verus_spec_attr(attrs);
    let with = sig.spec.with.as_ref().or(attr.as_ref().and_then(|a| a.spec.with.as_ref()));
    let params: Vec<Param> = sig.inputs.iter()
        .chain(with.into_iter().flat_map(|w| w.inputs.iter()))
        .filter_map(|a| param(a, cx))
        .collect();
    // return type, including ghost return values
    let mut out = Lts::default();
    if let ReturnType::Type(_, _, _, t) = &sig.output { type_lts(t, cx, &mut out); }
    if let Some(w) = with {
        if let Some((_, outs)) = &w.outputs { for pt in outs { type_lts(&pt.ty, cx, &mut out); } }
    }
    if out.has_self {
        if let Some(st) = impl_self {
            let mut l = Lts::default();
            type_lts(st, cx, &mut l);
            out.named.extend(l.named);   // `'_` in an impl header is not elidable to a parameter
        }
    }
    // elision: a reference receiver wins; otherwise the only input lifetime
    let receiver_ref = params.iter().position(|p| p.receiver && p.refl.is_some());
    let elision_target = receiver_ref.or_else(|| {
        let n: usize = params.iter().map(|p| p.lts.named.len() + p.lts.elided as usize).sum();
        if n == 1 { params.iter().position(|p| matches!(p.refl, Some((RefLt::Elided, _)))) } else { None }
    });
    // An associated type in the result (`Self::RefPermission`, `<T as Tr>::X`,
    // `T::X`) may hide a named lifetime (`type RefPermission =
    // BoxPointsToRef<'a, T>`): a parameter with a named lifetime may flow into it.
    // Only with all_refs (item-index --full), so that the item index stays as it was.
    let tparams: Vec<String> = sig.generics.type_params().map(|t| t.ident.to_string()).collect();
    let mut proj = false;
    if all_refs {
        if let ReturnType::Type(_, _, _, t) = &sig.output { proj |= has_projection(t, &tparams); }
        if let Some((_, outs)) = with.and_then(|w| w.outputs.as_ref()) {
            for pt in outs { proj |= has_projection(&pt.ty, &tparams); }
        }
    }
    params.iter().enumerate()
        .filter_map(|(i, p)| {
            let (l, is_mut) = p.refl.clone()?;
            if !is_mut && !all_refs { return None }
            let flows = match l {
                RefLt::Named(n) => out.named.contains(&n) || (proj && n != "static"),
                RefLt::Elided => out.elided && elision_target == Some(i),
            };
            Some((p.name.clone(), is_mut, flows))
        })
        .collect()
}

/// Whether a type mentions an associated type: a qualified path, or a path
/// of two or more segments starting with `Self` or a type parameter.
fn has_projection(t: &Type, tparams: &[String]) -> bool {
    match t {
        Type::Path(p) => {
            if p.qself.is_some() { return true }
            let segs: Vec<String> = p.path.segments.iter().map(|s| s.ident.to_string()).collect();
            if segs.len() >= 2 && (segs[0] == "Self" || tparams.contains(&segs[0])) { return true }
            p.path.segments.iter().any(|seg| match &seg.arguments {
                PathArguments::AngleBracketed(a) => a.args.iter().any(|arg| match arg {
                    GenericArgument::Type(t) => has_projection(t, tparams),
                    _ => false,
                }),
                _ => false,
            })
        }
        Type::Reference(r) => has_projection(&r.elem, tparams),
        Type::Tuple(x) => x.elems.iter().any(|e| has_projection(e, tparams)),
        Type::Array(x) => has_projection(&x.elem, tparams),
        Type::Slice(x) => has_projection(&x.elem, tparams),
        Type::Paren(x) => has_projection(&x.elem, tparams),
        Type::Group(x) => has_projection(&x.elem, tparams),
        _ => false,
    }
}

// ================================================================ items

fn emit(cx: &mut Cx, path: &str, module: &str, sig: &Signature, attrs: &[verus_syn::Attribute],
        span: proc_macro2::Span, self_ty: Option<&Type>, tr: Option<String>, in_trait: Option<String>) {
    let muts: String = mut_flows(sig, attrs, self_ty, cx).iter()
        .map(|(n, f)| format!(" ({} {})", s(n), if *f { "#t" } else { "#f" }))
        .collect();
    cx.out.push_str(&format!(
        "(item (file {}) (name {}) (start {}) (end {}) (self {}) (trait {}) (in-trait {}) (module {}) (muts{}))\n",
        s(path), s(&sig.ident.to_string()), span.start().line, span.end().line,
        opt(&self_ty.map(text)), opt(&tr), opt(&in_trait), s(module), muts));
}

/// A static has no signature; Verus turns an `exec static` into a function
/// of the same name.
fn emit_static(cx: &mut Cx, path: &str, module: &str, name: &str, span: proc_macro2::Span) {
    cx.out.push_str(&format!(
        "(item (file {}) (name {}) (start {}) (end {}) (self #f) (trait #f) (in-trait #f) (module {}) (muts))\n",
        s(path), s(name), span.start().line, span.end().line, s(module)));
}

fn is_verus(m: &verus_syn::ItemMacro) -> bool {
    m.mac.path.segments.last().map_or(false, |seg| seg.ident == "verus")
}

fn walk(path: &str, module: &str, items: &[Item], cx: &mut Cx) {
    for item in items {
        match item {
            Item::Fn(f) => emit(cx, path, module, &f.sig, &f.attrs, f.span(), None, None, None),
            Item::Static(st) => emit_static(cx, path, module, &st.ident.to_string(), st.span()),
            Item::Impl(i) => {
                let tr = i.trait_.as_ref().map(|(_, p, _)| text(p));
                for it in &i.items {
                    if let ImplItem::Fn(f) = it {
                        emit(cx, path, module, &f.sig, &f.attrs, f.span(), Some(&i.self_ty), tr.clone(), None);
                    }
                }
            }
            Item::Trait(t) => {
                for it in &t.items {
                    if let TraitItem::Fn(f) = it {
                        emit(cx, path, module, &f.sig, &f.attrs, f.span(), None, None, Some(t.ident.to_string()));
                    }
                }
            }
            Item::Mod(m) => {
                if let Some((_, inner)) = &m.content {
                    let sub = if module.is_empty() { m.ident.to_string() } else { format!("{module}::{}", m.ident) };
                    walk(path, &sub, inner, cx);
                }
            }
            // the body of `verus! { ... }` is itself a sequence of items
            Item::Macro(m) if is_verus(m) => {
                match verus_syn::parse2::<verus_syn::File>(m.mac.tokens.clone()) {
                    Ok(f) => walk(path, module, &f.items, cx),
                    Err(e) => eprintln!("{path}: verus! parse error: {e}"),
                }
            }
            _ => {}
        }
    }
}

/// The tokens of a `verus! { }` macro, rejoined as Verus does (`!is`, `!has`,
/// `!==`) when `rejoin` is set: without it, files using them do not parse.
pub(crate) fn macro_tokens(m: &verus_syn::ItemMacro, rejoin: bool) -> proc_macro2::TokenStream {
    if rejoin { verus_syn::rejoin_tokens(m.mac.tokens.clone()) } else { m.mac.tokens.clone() }
}
