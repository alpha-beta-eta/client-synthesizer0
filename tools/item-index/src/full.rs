//! `item-index --full FILE..`: what the source says that VIR does not
//! (docs/representation.md, step 1).  For every function (free, in an impl,
//! declared in a trait, inside `verus! { }` or with `#[verus_spec]`):
//!
//!   (fn (file F) (name N) (span S) (module M) (self T|#f) (trait T|#f) (in-trait T|#f)
//!       (mode spec|spec-checked|proof|proof-axiom|exec|default)
//!       (publish open|closed|open-restricted|uninterp|default)
//!       (attrs "external_body" ..)        the `#[verifier::..]` attributes and `#[verus_spec]`
//!       (generics "<..>") (where "..") (lifetimes "a" ..)
//!       (outer-generics "<..>") (outer-where "..") (outer-lifetimes "a" ..)   the impl's or trait's
//!       (params P ..) (with-in P ..) (with-out P ..)
//!       (ret NAME|#f "TYPE"|#f)
//!       (flows (NAME mut|shared #t|#f) ..)   may the result borrow the reference parameter
//!       (requires C ..) (ensures C ..) (returns C ..) (recommends C ..) (default-ensures C ..)
//!       (sig "the signature as written"))
//!   P = (p NAME "TYPE" REF (lts "a" ..) (elided #t|#f))
//!       REF = #f | (ref "a"|"_" mut|shared)   the outermost reference, through Tracked/Ghost
//!   C = (c S "TEXT" AST)                      one clause: its span, its source text, its tree
//!   S = "FILE:LINE:COL: LINE:COL"            as VIR writes spans (COL counts from 1)
//!
//!   (datatype (file F) (name N) (span S) (module M) (kind struct|enum|union)
//!             (lifetimes "a" ..) (type-params "T" ..) (generics "<..>")
//!             (fields (f NAME "VIS" "TYPE") ..) (variants "V" ..))
//!   (drop-impl (file F) (type "T"))         an `impl Drop for T`
//!
//! The AST is the source's, names as written:
//!   (path "TEXT") (lit "TEXT") (op "==" A B) (not A) (neg A) (deref A)
//!   (forall ((x "T") ..) BODY) (exists ..) (choose ..)     quantifiers; BODY under the
//!       inner attributes: (with-triggers (group A ..) .. B) for `#![trigger a, ..]`,
//!       (quant-attr "auto"|"all_triggers" B); (trigger A) for `#[trigger] a`
//!   (call F A ..) (method RECV "m" "TURBOFISH"|#f A ..) (field A "m") (arrow A "m")
//!   (index A I) (as A "T") (ref A) (ref-mut A) (tuple A ..) (view A) (final A)
//!   (is A "V") (isnt A "V") (has A B) (matches A (pat "TEXT" "x" ..) [OP B])
//!   (big-and A ..) (big-or A ..) (if C T E) (paren A) (src "TEXT")   anything else, as text
//! `(pat "TEXT" NAME ..)` lists the names the pattern binds.

use quote::ToTokens;
use std::collections::HashMap;
use verus_syn::{
    spanned::Spanned, BinOp, Expr, FnArg, FnArgKind, Generics, ImplItem, Item, Pat, ReturnType,
    Signature, Stmt, TraitItem, Type, UnOp,
};

use crate::{is_verus, outer_ref, s, text, type_lts, verus_spec_attr, Cx, Lts, RefLt};

/// The source of the file being walked, for the text of spans.
pub struct Src { pub path: String, pub lines: Vec<Vec<char>> }

impl Src {
    pub fn new(path: &str, src: &str) -> Src {
        Src { path: path.to_string(), lines: src.lines().map(|l| l.chars().collect()).collect() }
    }

    /// "FILE:L:C: L:C" (columns from 1, as VIR prints them)
    fn span(&self, sp: proc_macro2::Span) -> String {
        let (a, b) = (sp.start(), sp.end());
        format!("{}:{}:{}: {}:{}", self.path, a.line, a.column + 1, b.line, b.column + 1)
    }

    /// The span of a syntax node, from all its tokens: `Spanned::span` joins
    /// the first and last token's spans, and when the join fails it is the
    /// first token's alone (`valid_frame_paddr(..) ==> .. ==> may_panic()`
    /// came out as `valid_frame_paddr`).
    fn extent(&self, e: &Expr) -> String {
        // the clause's own attributes (`#[trigger] x.f().contains(m)`) are not in
        // VIR's span; an operand's (`#[trigger] f(i) % N == 0`, the attribute is
        // the call's) are
        let mut ts: Vec<proc_macro2::TokenTree> = e.to_token_stream().into_iter().collect();
        let mut n = own_attrs(e);
        while n > 0 && ts.len() > 2 && matches!(&ts[0], proc_macro2::TokenTree::Punct(p) if p.as_char() == '#')
            && matches!(&ts[1], proc_macro2::TokenTree::Group(g) if g.delimiter() == proc_macro2::Delimiter::Bracket) {
            ts.drain(0..2);
            n -= 1;
        }
        let (a, b) = extent(ts.into_iter().collect());
        format!("{}:{}:{}: {}:{}", self.path, a.0, a.1 + 1, b.0, b.1 + 1)
    }

    /// The source text a syntax node covers; when it has no location, the tokens.
    fn text_of<T: verus_syn::spanned::Spanned + quote::ToTokens>(&self, t: &T) -> String {
        let (a, b) = extent(t.to_token_stream());
        let (a, b) = (proc_macro2::LineColumn { line: a.0, column: a.1 }, proc_macro2::LineColumn { line: b.0, column: b.1 });
        if a.line == 0 || b.line == 0 || a.line > self.lines.len() || b.line > self.lines.len() {
            return text(t);
        }
        let mut out = String::new();
        for l in a.line..=b.line {
            let line = &self.lines[l - 1];
            let from = if l == a.line { a.column.min(line.len()) } else { 0 };
            let to = if l == b.line { b.column.min(line.len()) } else { line.len() };
            if from < to { out.extend(&line[from..to]); }
            if l != b.line { out.push(' '); }
        }
        let mut r = out.split_whitespace().collect::<Vec<_>>().join(" ");
        if r.is_empty() { r = text(t); }
        r
    }
}

/// The number of outer attributes the expression itself has (not its operands').
fn own_attrs(e: &Expr) -> usize {
    match e {
        Expr::MethodCall(x) => x.attrs.len(), Expr::Call(x) => x.attrs.len(), Expr::Field(x) => x.attrs.len(),
        Expr::Binary(x) => x.attrs.len(), Expr::Unary(x) => x.attrs.len(), Expr::Paren(x) => x.attrs.len(),
        Expr::Path(x) => x.attrs.len(), Expr::Index(x) => x.attrs.len(), Expr::Lit(x) => x.attrs.len(),
        Expr::Cast(x) => x.attrs.len(), Expr::Reference(x) => x.attrs.len(), Expr::Tuple(x) => x.attrs.len(),
        Expr::If(x) => x.attrs.len(), Expr::Block(x) => x.attrs.len(), Expr::Match(x) => x.attrs.len(),
        Expr::View(x) => x.attrs.len(), Expr::GetField(x) => x.attrs.len(), Expr::Is(x) => x.attrs.len(),
        Expr::IsNot(x) => x.attrs.len(), Expr::Matches(x) => x.attrs.len(), Expr::Has(x) => x.attrs.len(),
        Expr::Final(x) => x.attrs.len(),
        _ => 0,
    }
}

/// The first start and the last end of a token stream's tokens, as (line, column);
/// (0, 0) when no token has a location.
fn extent(ts: proc_macro2::TokenStream) -> ((usize, usize), (usize, usize)) {
    let mut lo = (usize::MAX, usize::MAX);
    let mut hi = (0usize, 0usize);
    fn walk(ts: proc_macro2::TokenStream, lo: &mut (usize, usize), hi: &mut (usize, usize)) {
        for tt in ts {
            let spans = match &tt {
                proc_macro2::TokenTree::Group(g) => {
                    walk(g.stream(), lo, hi);
                    vec![g.span_open(), g.span_close()]
                }
                t => vec![t.span()],
            };
            for sp in spans {
                let (a, b) = (sp.start(), sp.end());
                // tokens made by the parser (a joined `==>`) have a zero-width call-site span
                if a.line == 0 || (a.line, a.column) == (b.line, b.column) { continue }
                if (a.line, a.column) < *lo { *lo = (a.line, a.column); }
                if (b.line, b.column) > *hi { *hi = (b.line, b.column); }
            }
        }
    }
    walk(ts, &mut lo, &mut hi);
    if lo.0 == usize::MAX { ((0, 0), (0, 0)) } else { (lo, hi) }
}

// ================================================================ expressions

fn binop(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add(_) => "+", BinOp::Sub(_) => "-", BinOp::Mul(_) => "*", BinOp::Div(_) => "/",
        BinOp::Rem(_) => "%", BinOp::And(_) => "&&", BinOp::Or(_) => "||", BinOp::BitXor(_) => "^",
        BinOp::BitAnd(_) => "&", BinOp::BitOr(_) => "|", BinOp::Shl(_) => "<<", BinOp::Shr(_) => ">>",
        BinOp::Eq(_) => "==", BinOp::Lt(_) => "<", BinOp::Le(_) => "<=", BinOp::Ne(_) => "!=",
        BinOp::Ge(_) => ">=", BinOp::Gt(_) => ">", BinOp::Equiv(_) => "<==>", BinOp::Imply(_) => "==>",
        BinOp::Exply(_) => "<==", BinOp::BigEq(_) => "===", BinOp::BigNe(_) => "!==",
        BinOp::ExtEq(_) => "=~=", BinOp::ExtNe(_) => "!~=", BinOp::ExtDeepEq(_) => "=~~=",
        BinOp::ExtDeepNe(_) => "!~~=",
        _ => "?=",
    }
}

/// The names a pattern binds.
pub fn pat_names(p: &Pat, acc: &mut Vec<String>) {
    match p {
        Pat::Ident(i) => {
            acc.push(i.ident.to_string());
            if let Some((_, sub)) = &i.subpat { pat_names(sub, acc) }
        }
        Pat::TupleStruct(t) => for e in &t.elems { pat_names(e, acc) },
        Pat::Tuple(t) => for e in &t.elems { pat_names(e, acc) },
        Pat::Struct(st) => for f in &st.fields { pat_names(&f.pat, acc) },
        Pat::Slice(sl) => for e in &sl.elems { pat_names(e, acc) },
        Pat::Or(o) => if let Some(c) = o.cases.first() { pat_names(c, acc) },
        Pat::Paren(x) => pat_names(&x.pat, acc),
        Pat::Reference(x) => pat_names(&x.pat, acc),
        Pat::Type(x) => pat_names(&x.pat, acc),
        _ => {}
    }
}

fn pat(p: &Pat, src: &Src) -> String {
    let mut names = Vec::new();
    pat_names(p, &mut names);
    let ns: String = names.iter().map(|n| format!(" {}", s(n))).collect();
    format!("(pat {}{})", s(&src.text_of(p)), ns)
}

fn args<'a>(es: impl Iterator<Item = &'a Expr>, src: &Src) -> String {
    es.map(|e| format!(" {}", ast(e, src))).collect()
}

/// A block that is a single expression is that expression.
fn block_expr(b: &verus_syn::Block, src: &Src) -> String {
    match b.stmts.as_slice() {
        [Stmt::Expr(e, None)] => ast(e, src),
        _ => format!("(src {})", s(&src.text_of(b))),
    }
}

/// The expression's own outer attributes (not its operands').
fn expr_attrs(e: &Expr) -> &[verus_syn::Attribute] {
    match e {
        Expr::MethodCall(x) => &x.attrs, Expr::Call(x) => &x.attrs, Expr::Field(x) => &x.attrs,
        Expr::Binary(x) => &x.attrs, Expr::Unary(x) => &x.attrs, Expr::Paren(x) => &x.attrs,
        Expr::Path(x) => &x.attrs, Expr::Index(x) => &x.attrs, Expr::Lit(x) => &x.attrs,
        Expr::Cast(x) => &x.attrs, Expr::Reference(x) => &x.attrs, Expr::Tuple(x) => &x.attrs,
        Expr::If(x) => &x.attrs, Expr::Block(x) => &x.attrs, Expr::Match(x) => &x.attrs,
        Expr::View(x) => &x.attrs, Expr::GetField(x) => &x.attrs, Expr::Is(x) => &x.attrs,
        Expr::IsNot(x) => &x.attrs, Expr::Matches(x) => &x.attrs, Expr::Has(x) => &x.attrs,
        Expr::Final(x) => &x.attrs,
        _ => &[],
    }
}

fn attr_name(a: &verus_syn::Attribute) -> String {
    let p = a.path();
    if p.segments.len() == 1 { p.segments[0].ident.to_string() } else { String::new() }
}

/// With `--full-spans`, every node is (@ "SPAN" NODE), SPAN its tokens' extent
/// without its own attributes (as VIR's spans are).
pub static NODE_SPANS: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// `(trigger E)` for an expression marked `#[trigger]`.
pub fn ast(e: &Expr, src: &Src) -> String {
    let a = ast0(e, src);
    let a = if NODE_SPANS.load(std::sync::atomic::Ordering::Relaxed) {
        // VIR's span of an operand includes its attributes (`#[trigger] f(i) % N`),
        // a clause's does not: with attributes, both (@ SPAN NODE SPAN-WITH-ATTRS)
        if own_attrs(e) > 0 {
            let (a0, b0) = extent(e.to_token_stream());
            let full = format!("{}:{}:{}: {}:{}", src.path, a0.0, a0.1 + 1, b0.0, b0.1 + 1);
            format!("(@ {} {} {})", s(&src.extent(e)), a, s(&full))
        } else {
            format!("(@ {} {})", s(&src.extent(e)), a)
        }
    } else {
        a
    };
    if expr_attrs(e).iter().any(|x| matches!(x.style, verus_syn::AttrStyle::Outer) && attr_name(x) == "trigger") {
        format!("(trigger {})", a)
    } else {
        a
    }
}

/// A quantifier's body under its inner attributes: `#![trigger a, b]` is
/// (with-triggers (group A B) .. BODY), `#![auto]` (quant-attr "auto" BODY).
fn quant_body(c: &verus_syn::ExprClosure, src: &Src) -> String {
    let body = ast(&c.body, src);
    let mut groups = Vec::new();
    let mut flags = Vec::new();
    for a in &c.inner_attrs {
        match attr_name(a).as_str() {
            "trigger" => {
                let es = match &a.meta {
                    verus_syn::Meta::List(l) => l.parse_args_with(
                        verus_syn::punctuated::Punctuated::<Expr, verus_syn::Token![,]>::parse_terminated).ok(),
                    _ => None,
                };
                match es {
                    Some(es) => groups.push(format!("(group{})", args(es.iter(), src))),
                    None => return format!("(src {})", s(&src.text_of(c))),
                }
            }
            n @ ("auto" | "all_triggers") => flags.push(n.to_string()),
            _ => {}
        }
    }
    if !groups.is_empty() {
        format!("(with-triggers {} {})", groups.join(" "), body)
    } else if let Some(f) = flags.first() {
        format!("(quant-attr {} {})", s(f), body)
    } else {
        body
    }
}

fn ast0(e: &Expr, src: &Src) -> String {
    let raw = || format!("(src {})", s(&src.text_of(e)));
    match e {
        // kept: Verus treats `a && (b matches P && c)` and `a && b matches P && c` differently
        Expr::Paren(x) => format!("(paren {})", ast(&x.expr, src)),
        Expr::Group(x) => ast(&x.expr, src),
        Expr::Path(_) => format!("(path {})", s(&src.text_of(e))),
        Expr::Lit(_) => format!("(lit {})", s(&src.text_of(e))),
        Expr::Binary(b) => format!("(op {} {} {})", s(binop(&b.op)), ast(&b.left, src), ast(&b.right, src)),
        Expr::Unary(u) => match &u.op {
            UnOp::Not(_) => format!("(not {})", ast(&u.expr, src)),
            UnOp::Neg(_) => format!("(neg {})", ast(&u.expr, src)),
            UnOp::Deref(_) => format!("(deref {})", ast(&u.expr, src)),
            UnOp::Forall(_) | UnOp::Exists(_) | UnOp::Choose(_) => {
                let q = match &u.op { UnOp::Forall(_) => "forall", UnOp::Exists(_) => "exists", _ => "choose" };
                match &*u.expr {
                    Expr::Closure(c) => {
                        let bs: String = c.inputs.iter().map(|a| {
                            let mut ns = Vec::new();
                            pat_names(&a.pat, &mut ns);
                            let ty = match &a.pat { Pat::Type(t) => s(&text(&t.ty)), _ => "#f".to_string() };
                            ns.iter().map(|n| format!(" ({} {})", s(n), ty)).collect::<String>()
                        }).collect();
                        format!("({} ({}) {})", q, bs.trim_start(), quant_body(c, src))
                    }
                    _ => raw(),
                }
            }
            _ => raw(),
        },
        Expr::Call(c) => format!("(call {}{})", ast(&c.func, src), args(c.args.iter(), src)),
        Expr::MethodCall(m) => format!("(method {} {} {}{})", ast(&m.receiver, src), s(&m.method.to_string()),
                                       m.turbofish.as_ref().map(|t| s(&text(t))).unwrap_or_else(|| "#f".into()),
                                       args(m.args.iter(), src)),
        Expr::Field(f) => format!("(field {} {})", ast(&f.base, src), s(&text(&f.member))),
        Expr::GetField(f) => format!("(arrow {} {})", ast(&f.base, src), s(&text(&f.member))),
        Expr::Index(i) => format!("(index {} {})", ast(&i.expr, src), ast(&i.index, src)),
        Expr::Cast(c) => format!("(as {} {})", ast(&c.expr, src), s(&text(&c.ty))),
        Expr::Reference(r) => format!("({} {})", if r.mutability.is_some() { "ref-mut" } else { "ref" }, ast(&r.expr, src)),
        Expr::Tuple(t) => format!("(tuple{})", args(t.elems.iter(), src)),
        Expr::View(v) => format!("(view {})", ast(&v.expr, src)),
        Expr::Final(f) => format!("(final {})", ast(&f.arg, src)),
        Expr::Is(i) => format!("(is {} {})", ast(&i.base, src), s(&i.variant_ident.to_string())),
        Expr::IsNot(i) => format!("(isnt {} {})", ast(&i.base, src), s(&i.variant_ident.to_string())),
        Expr::Has(h) => format!("(has {} {})", ast(&h.lhs, src), ast(&h.rhs, src)),
        Expr::HasNot(h) => format!("(not (has {} {}))", ast(&h.lhs, src), ast(&h.rhs, src)),
        Expr::Matches(m) => {
            let rest = match &m.op_expr {
                Some(o) => {
                    let op = match &o.op_token {
                        verus_syn::MatchesOpToken::Implies(_) => "==>",
                        verus_syn::MatchesOpToken::AndAnd(_) => "&&",
                        verus_syn::MatchesOpToken::BigAnd => "&&&",
                    };
                    format!(" {} {}", s(op), ast(&o.rhs, src))
                }
                None => String::new(),
            };
            format!("(matches {} {}{})", ast(&m.lhs, src), pat(&m.pat, src), rest)
        }
        Expr::BigAnd(b) => format!("(big-and{})", args(b.exprs.iter().map(|x| &*x.expr), src)),
        Expr::BigOr(b) => format!("(big-or{})", args(b.exprs.iter().map(|x| &*x.expr), src)),
        Expr::If(i) => {
            let els = match &i.else_branch {
                Some((_, e)) => match &**e { Expr::Block(b) => block_expr(&b.block, src), e => ast(e, src) },
                None => "#f".into(),
            };
            format!("(if {} {} {})", ast(&i.cond, src), block_expr(&i.then_branch, src), els)
        }
        Expr::Block(b) if b.block.stmts.len() == 1 => block_expr(&b.block, src),
        _ => raw(),
    }
}

// ================================================================ functions

fn clauses(tag: &str, es: Option<&verus_syn::punctuated::Punctuated<Expr, verus_syn::Token![,]>>, src: &Src) -> String {
    let body: String = es.into_iter().flat_map(|p| p.iter())
        .map(|e| format!(" (c {} {} {})", s(&src.extent(e)), s(&src.text_of(e)), ast(e, src)))
        .collect();
    format!(" ({}{})", tag, body)
}

fn lts_text(l: &Lts) -> String {
    let named: String = l.named.iter().map(|n| format!(" {}", s(n))).collect();
    format!("(lts{}) (elided {})", named, if l.elided { "#t" } else { "#f" })
}

fn param_rec(a: &FnArg, cx: &Cx, src: &Src) -> Option<String> {
    let (name, ty): (String, &Type) = match &a.kind {
        FnArgKind::Receiver(r) => ("self".into(), &r.ty),
        FnArgKind::Typed(pt) => (crate::pat_name(&pt.pat)?, &pt.ty),
    };
    let mut l = Lts::default();
    type_lts(ty, cx, &mut l);
    let r = match outer_ref(ty) {
        Some((RefLt::Named(n), m)) => format!("(ref {} {})", s(&n), if m { "mut" } else { "shared" }),
        Some((RefLt::Elided, m)) => format!("(ref \"_\" {})", if m { "mut" } else { "shared" }),
        None => "#f".into(),
    };
    let _ = src;
    Some(format!("(p {} {} {} {})", s(&name), s(&text(ty)), r, lts_text(&l)))
}

fn generics_text(g: &Generics) -> (String, String, String) {
    let params = if g.params.is_empty() { String::new() } else { text(&g.params) };
    let wh = g.where_clause.as_ref().map(text).unwrap_or_default();
    let lts: String = g.lifetimes().map(|l| format!(" {}", s(&l.lifetime.ident.to_string()))).collect();
    (params, wh, lts)
}

fn attr_names(attrs: &[verus_syn::Attribute]) -> String {
    let mut out = String::new();
    for a in attrs {
        let segs: Vec<String> = a.path().segments.iter().map(|x| x.ident.to_string()).collect();
        match segs.as_slice() {
            [v, n] if v == "verifier" => out.push_str(&format!(" {}", s(n))),
            [n] if n == "verus_spec" || n == "verus_verify" || n == "trigger" => out.push_str(&format!(" {}", s(n))),
            _ => {}
        }
        // `#[verifier(external_body)]`
        if segs.as_slice() == ["verifier"] {
            if let verus_syn::Meta::List(l) = &a.meta { out.push_str(&format!(" {}", s(&l.tokens.to_string()))); }
        }
    }
    out
}

fn mode_name(m: &verus_syn::FnMode) -> &'static str {
    match m {
        verus_syn::FnMode::Spec(_) => "spec", verus_syn::FnMode::SpecChecked(_) => "spec-checked",
        verus_syn::FnMode::Proof(_) => "proof", verus_syn::FnMode::ProofAxiom(_) => "proof-axiom",
        verus_syn::FnMode::Exec(_) => "exec", verus_syn::FnMode::Default => "default",
    }
}

fn publish_name(p: &verus_syn::Publish) -> &'static str {
    match p {
        verus_syn::Publish::Closed(_) => "closed", verus_syn::Publish::Open(_) => "open",
        verus_syn::Publish::OpenRestricted(_) => "open-restricted", verus_syn::Publish::Uninterp(_) => "uninterp",
        verus_syn::Publish::Default => "default",
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_fn(cx: &mut Cx, src: &Src, module: &str, sig: &Signature, attrs: &[verus_syn::Attribute],
           span: proc_macro2::Span, self_ty: Option<&Type>, tr: Option<String>, in_trait: Option<String>,
           outer: Option<&Generics>) {
    // the spec: in `verus!` syntax on the signature, else in `#[verus_spec(..)]`
    // (or both: `#[verus_spec(with ..)]` with `requires`/`ensures` on the signature), clause by clause
    let attr = verus_spec_attr(attrs);
    let pick = |a: Option<&verus_syn::SignatureSpec>| -> verus_syn::SignatureSpec {
        let mut m = sig.spec.clone();
        if let Some(a) = a {
            if a.requires.is_some() { m.requires = a.requires.clone(); }
            if a.ensures.is_some() { m.ensures = a.ensures.clone(); }
            if a.returns.is_some() { m.returns = a.returns.clone(); }
            if a.recommends.is_some() { m.recommends = a.recommends.clone(); }
            if a.default_ensures.is_some() { m.default_ensures = a.default_ensures.clone(); }
        }
        m
    };
    let merged = pick(attr.as_ref().map(|a| &a.spec));
    let spec = &merged;
    let with = sig.spec.with.as_ref().or(attr.as_ref().and_then(|a| a.spec.with.as_ref()));
    let ins: String = sig.inputs.iter().filter_map(|a| param_rec(a, cx, src)).map(|p| format!(" {p}")).collect();
    let with_in: String = with.into_iter().flat_map(|w| w.inputs.iter())
        .filter_map(|a| param_rec(a, cx, src)).map(|p| format!(" {p}")).collect();
    let with_out: String = with.and_then(|w| w.outputs.as_ref()).into_iter().flat_map(|(_, o)| o.iter())
        .map(|pt| {
            let mut l = Lts::default();
            type_lts(&pt.ty, cx, &mut l);
            format!(" (p {} {} #f {})", s(&crate::pat_name(&pt.pat).unwrap_or_default()), s(&text(&pt.ty)), lts_text(&l))
        }).collect();
    // the result's name: `-> (r: T)` in verus! syntax, `r =>` in the attribute
    let (rname, rty) = match &sig.output {
        ReturnType::Type(_, _, named, t) => (named.as_ref().and_then(|b| crate::pat_name(&b.1)), Some(text(&**t))),
        ReturnType::Default => (None, None),
    };
    let rname = rname.or_else(|| attr.as_ref().and_then(|a| a.ret_pat.as_ref()).and_then(|(p, _)| crate::pat_name(p)));
    let (gp, wh, lts) = generics_text(&sig.generics);
    let mut out = format!(
        "(fn (file {}) (name {}) (span {}) (module {}) (self {}) (trait {}) (in-trait {}) (mode {}) (publish {}) (attrs{})",
        s(&src.path), s(&sig.ident.to_string()), s(&src.span(span)), s(module),
        crate::opt(&self_ty.map(text)), crate::opt(&tr), crate::opt(&in_trait),
        mode_name(&sig.mode), publish_name(&sig.publish), attr_names(attrs));
    out.push_str(&format!(" (generics {}) (where {}) (lifetimes{})", s(&gp), s(&wh), lts));
    // the enclosing impl's or trait's generics (`impl<'a> VmSpace<'a>`: the method's `'a`)
    let (ogp, owh, olts) = outer.map(generics_text).unwrap_or_default();
    out.push_str(&format!(" (outer-generics {}) (outer-where {}) (outer-lifetimes{})", s(&ogp), s(&owh), olts));
    out.push_str(&format!(" (params{}) (with-in{}) (with-out{})", ins, with_in, with_out));
    out.push_str(&format!(" (ret {} {})", crate::opt(&rname), crate::opt(&rty)));
    // which reference parameters (shared and &mut, the `with` ones too) the result may borrow
    let flows: String = crate::ref_flows(sig, attrs, self_ty, cx, true).iter()
        .map(|(n, m, fl)| format!(" ({} {} {})", s(n), if *m { "mut" } else { "shared" }, if *fl { "#t" } else { "#f" }))
        .collect();
    out.push_str(&format!(" (flows{})", flows));
    out.push_str(&clauses("requires", spec.requires.as_ref().map(|r| &r.exprs.exprs), src));
    out.push_str(&clauses("ensures", spec.ensures.as_ref().map(|r| &r.exprs.exprs), src));
    out.push_str(&clauses("returns", spec.returns.as_ref().map(|r| &r.exprs.exprs), src));
    out.push_str(&clauses("recommends", spec.recommends.as_ref().map(|r| &r.exprs.exprs), src));
    out.push_str(&clauses("default-ensures", spec.default_ensures.as_ref().map(|r| &r.exprs.exprs), src));
    // the signature as written: from the start of the function to its spec or body
    let mut sig_only = sig.clone();
    sig_only.spec = verus_syn::SignatureSpec {
        prover: None, atomic_spec: None, requires: None, recommends: None, ensures: None,
        default_ensures: None, returns: None, decreases: None, invariants: None, unwind: None,
        with: sig.spec.with.clone(),
    };
    out.push_str(&format!(" (sig {}))\n", s(&src.text_of(&sig_only))));
    cx.out.push_str(&out);
}

fn emit_datatype(cx: &mut Cx, src: &Src, module: &str, item: &Item) {
    let (kind, name, g, span, fields, variants): (&str, String, &Generics, proc_macro2::Span, Vec<String>, Vec<String>) = match item {
        Item::Struct(x) => ("struct", x.ident.to_string(), &x.generics, x.span(),
                            x.fields.iter().enumerate().map(|(i, f)| format!("(f {} {} {})",
                                s(&f.ident.as_ref().map(|i| i.to_string()).unwrap_or(i.to_string())),
                                s(&text(&f.vis)), s(&text(&f.ty)))).collect(), vec![]),
        Item::Enum(x) => ("enum", x.ident.to_string(), &x.generics, x.span(), vec![],
                          x.variants.iter().map(|v| s(&v.ident.to_string())).collect()),
        Item::Union(x) => ("union", x.ident.to_string(), &x.generics, x.span(), vec![], vec![]),
        _ => return,
    };
    let (gp, _, lts) = generics_text(g);
    let tps: String = g.type_params().map(|t| format!(" {}", s(&t.ident.to_string()))).collect();
    cx.out.push_str(&format!(
        "(datatype (file {}) (name {}) (span {}) (module {}) (kind {}) (lifetimes{}) (type-params{}) (generics {}) (fields {}) (variants {}))\n",
        s(&src.path), s(&name), s(&src.span(span)), s(module), kind, lts, tps, s(&gp),
        fields.join(" "), variants.join(" ")));
}

/// `(const (file F) (name N) (span S) (module M) (self T|#f) (trait T|#f) (in-trait T|#f) (kind const|static) (type "T"))`:
/// VIR makes a function of every const and static.
#[allow(clippy::too_many_arguments)]
fn emit_const(cx: &mut Cx, src: &Src, module: &str, name: &str, ty: &Type, span: proc_macro2::Span, kind: &str,
              self_ty: Option<&Type>, tr: Option<String>, in_trait: Option<String>) {
    cx.out.push_str(&format!(
        "(const (file {}) (name {}) (span {}) (module {}) (self {}) (trait {}) (in-trait {}) (kind {}) (type {}))\n",
        s(&src.path), s(name), s(&src.span(span)), s(module), crate::opt(&self_ty.map(text)), crate::opt(&tr),
        crate::opt(&in_trait), kind, s(&text(ty))));
}

pub fn walk_full(src: &Src, module: &str, items: &[Item], cx: &mut Cx, seen: &mut HashMap<String, ()>) {
    for item in items {
        match item {
            Item::Fn(f) => emit_fn(cx, src, module, &f.sig, &f.attrs, f.span(), None, None, None, None),
            Item::Const(c) => emit_const(cx, src, module, &c.ident.to_string(), &c.ty, c.span(), "const", None, None, None),
            Item::Static(c) => emit_const(cx, src, module, &c.ident.to_string(), &c.ty, c.span(), "static", None, None, None),
            Item::Struct(_) | Item::Enum(_) | Item::Union(_) => emit_datatype(cx, src, module, item),
            Item::Impl(i) => {
                let tr = i.trait_.as_ref().map(|(_, p, _)| text(p));
                if tr.as_deref().map_or(false, |t| t == "Drop" || t.ends_with("::Drop")) {
                    cx.out.push_str(&format!("(drop-impl (file {}) (type {}))\n", s(&src.path), s(&text(&*i.self_ty))));
                }
                for it in &i.items {
                    match it {
                        ImplItem::Fn(f) => emit_fn(cx, src, module, &f.sig, &f.attrs, f.span(), Some(&i.self_ty), tr.clone(), None, Some(&i.generics)),
                        ImplItem::Const(c) => emit_const(cx, src, module, &c.ident.to_string(), &c.ty, c.span(), "const",
                                                         Some(&i.self_ty), tr.clone(), None),
                        _ => {}
                    }
                }
            }
            Item::Trait(t) => {
                for it in &t.items {
                    match it {
                        TraitItem::Fn(f) => emit_fn(cx, src, module, &f.sig, &f.attrs, f.span(), None, None, Some(t.ident.to_string()), Some(&t.generics)),
                        TraitItem::Const(c) => emit_const(cx, src, module, &c.ident.to_string(), &c.ty, c.span(), "const",
                                                          None, None, Some(t.ident.to_string())),
                        _ => {}
                    }
                }
            }
            Item::Mod(m) => {
                if let Some((_, inner)) = &m.content {
                    let sub = if module.is_empty() { m.ident.to_string() } else { format!("{module}::{}", m.ident) };
                    walk_full(src, &sub, inner, cx, seen);
                }
            }
            Item::Macro(m) if is_verus(m) => {
                match verus_syn::parse2::<verus_syn::File>(crate::macro_tokens(m, cx.rejoin)) {
                    Ok(f) => walk_full(src, module, &f.items, cx, seen),
                    Err(e) => eprintln!("{}:{}:{}: verus! parse error: {e}", src.path, e.span().start().line, e.span().start().column + 1),
                }
            }
            _ => {}
        }
    }
}

/// `item-index --expr`: the tree of one expression read from stdin (spans
/// are of the text read).
pub fn parse_expr(input: &str) -> Result<String, String> {
    let tokens: proc_macro2::TokenStream = input.parse().map_err(|e: proc_macro2::LexError| e.to_string())?;
    let e: Expr = verus_syn::parse2(verus_syn::rejoin_tokens(tokens)).map_err(|e| e.to_string())?;
    let src = Src::new("<expr>", input);
    Ok(ast(&e, &src))
}
