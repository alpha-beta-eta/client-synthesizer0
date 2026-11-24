# 踩过的坑

本文收集一路上 (前身2026-11-06起, 到本版2026-11-22) 遇到的实现上的坑: 每条写**现象**, **原因**, **现在的做法或规则**. 按出问题的层次排列, 从环境, Verus, VIR和抽取, 到生成, 渲染运行, 分析确认; 最后是流程上的教训. 来源是[design.md](design.md)第4节, 前身的`docs/time-sinks.md`, `enumeration.md`, `triage.md`和提交记录; 详细的测量在那里.

先记三条总的教训, 下面很多条都是它们的实例:

- **每层的毛病在本层不报错, 在下游以别的样子出现.** VIR的格式变了表现为大批条目抽不出; 抽取的bug表现为一批同类条目编译不过; 知识过时表现为claim编译不过或空洞地通过. 所以每层都要有能出错的核对.
- **无声的错比有声的错危险.** 良构性规则过宽, 版本检查被绕过, 续跑沿用旧结果, 都不报错, 只让结论悄悄变坏. 汇总数字掩盖它们, 要逐个client比较.
- **慢的时候先测量, 不要先猜.** 三次先猜错了原因 (见A节).

## A. 环境 (Windows, WSL)

| 现象 | 原因 | 做法 |
|---|---|---|
| 表与检出的版本检查形同虚设 | WSL中`PATH`后接Windows的`PATH`, 先找到`git.exe`, 它看不到`/root/..`, HEAD为空串, 而空串是任何提交的前缀 | 只在Windows上找`git.exe`; HEAD为空时报错 |
| `fasl-read: incompatible fasl-object machine-type` | 同一仓库在Windows和WSL中用Racket, `compiled/`互相覆盖 | Windows上`PLTCOMPILEDROOTS="compiled/win;"` |
| 传给`wsl.exe`的`/mnt/..`, `/root/..`路径被改写 | Git Bash的路径转换 | `MSYS_NO_PATHCONV=1`; PowerShell的引号和`$`会弄坏bash命令, 写进`.sh`再调用 |
| 含反斜杠的脚本坏了 | shell的heredoc把反斜杠减半 | 用文件写 |
| 编辑后vostd源码的行尾变了 | `python`编辑改行尾; vostd源码是CRLF | 编辑保持行尾; 修改的OLD/NEW取所改文件的行尾 |
| 按字符位置剪切文件错位 | Racket开了行计数后把CRLF算一个位置 | 注意CRLF, 编辑前备份 |
| 编译Verus出`os error 1455`, 随后`only metadata stub found for rlib dependency core`等假错误 | 并行rustc耗尽可提交内存, 页面文件在快满的C盘上不能增长 | `CARGO_BUILD_JOBS=4` |
| 换了Verus后行为怪异 | 旧Verus的产物混进构建目录 | 换Verus就换`CARGO_TARGET_DIR` |
| 别处共用的Verus被换掉 | 新版`cargo dv bootstrap`把`cargo-verus`, `rust_verify`等装进全局`~/.cargo/bin` | 从Verus仓库另建worktree再bootstrap |
| Verus在Windows上对每个`#[verus_spec(with ..)]`的调用报"resolves to `f`, not to `f`" | `proof_with!`检查比较span时连parent一起比, Windows上parent不同 (Linux CI通过). 先怀疑CRLF和过期构建目录, 都不是 | 在最小例子上复现确认; 本地改为只比较起止位置; 最后全部移到WSL |
| 相对路径的`CS_ENV`: 每个证人都`not-run` | 环境第一次用到时才读, 那时当前目录已换成检出 | 启动时解析; 整片`not-run`先看`verus-1.out` |
| "vm_space的生成用了三小时" | 机器睡眠 (Kernel-Power 42/107), 生成实际32秒 | 每次尝试记`(seconds ..)` |
| `pkill -f`杀掉了自己 | 在`bash -lc`中`-f`匹配到自己的shell | 用`pgrep -x` |
| 被杀掉的运行留下`cs_clients.rs`, `mod cs_clients;`, 改过的`Cargo.lock`; 下一次VIR导出不干净 | 来不及清理 | 运行开始时清理 (只动未跟踪的`cs_clients.rs`和唯一改动是那一行的文件); 停掉后看`git status` |

## B. Verus的行为

### B.1 运行和输出

- **一个模块一个z3会话.** 不加属性时整个client模块在一个z3中**串行**验证, 会话一直累积, cursor模块约18分钟后崩溃 ("expected rlimit-count in smt statistics"), 对半拆7次, 一个模块3.5小时, 整轮7小时. 先误判为"批太大". 改为每个client`#[verifier::spinoff_prover]`: 整轮26分钟, 而且rlimit的结果不再取决于同批的别的client.
- **并行之后内存是限制.** 每个z3 200–350 MB, rust_verify约1.5 GB; 线程数按`/proc/meminfo`估.
- **`cargo dv verify`对见过的源码不再验证.** 只打印`Verified ostd .. in 0.59s`, 没有`verification results`行, 被当作失败. 它按**内容**判断, 改`lib.rs`的修改时间没用 (试过); 现在每次验证前在`lib.rs`末尾加一行带时间的注释 (不移动任何行, 错误行号不变), 验证后写回.
- **`cargo dv focus`在源码没变时给出上一次的结果, 即使`--verify-only-module`不同.** 确认修改时得出过错的结论. 看输出中"verifying module"是不是要的那个; 不可信时用整个crate的验证.
- **第一个`verification results`行可能是依赖的.** `cargo dv verify -p ostd`的日志中第一行是bitflags的 (44 verified), 被当作ostd的; ostd什么也没报时也会"通过". 取`-p "ostd"`之后的最后一行, 没有就是没有.
- **错误块只到下一条独立的提示.** 一个`error`之后到下一个`error`/`warning`之前的行不全是它的: `note: automatically chose triggers`的`-->`曾被当作错误位置, 把一处引理中的失败归给了恰好被打印触发器提示的frame-8, 使已确认的R54丢了两次.
- **`specs`的路径写成`ostd/src/../specs/..`.** 不先去掉`dir/..`, 错误对不上client模块, 所有client都像通过了 (前身因此把`specs::*`判为"不被验证", 一轮评估把它排除在外).
- **一个client的trigger错误使整个模块没有结果.** Verus遇到推断不出trigger的量词就不给验证结果, 运行器把"没有结果的运行中凡有错误的client"都当作编译错误丢掉, 而每个client都有失败的空洞断言: segment 786个client全记为compile-error, 总数上只是"编译错误多了". 现在只丢有非验证类错误的client.
- **只写`#![auto]`时**, Verus在源码标了触发器的地方推断不出, 整个模块编译不过; 源码的触发器要保留.
- **`--expand-errors`只展开每个函数中第一个失败的断言**; 后面的不透明子句仍按文本分组.
- **Verus会崩溃** (求解器panic, 内存耗尽). 崩溃的输出既不是编译错误也不能取部分结果; 对半拆开重跑只是后备.

### B.2 语义

- **`(sanity ok)`才可信.** 没有results行, 或sanity不恰好失败一次, 模块没有真的被验证; `not-verified`不能当作"全部失败"汇报.
- **失败的断言之后Verus假定它成立**: 后面的断言可能借光"通过", 后面的路径可能被报为空洞; 证否在有更早失败时也可能依赖它们.
- **空洞性断言只能在路径末尾**: 在分支末尾另加, 失败的`assert(false)`之后一切都空洞.
- **closed的spec体和私有字段对定义模块的子模块可见** (`is_body_visible_to`按路径前缀). client放在子模块时比真实调用者强, 一类缺陷系统地漏掉; 前身在一条判定 ("`split_spec`是closed, 调用者得不到`inv`") 突然在r28通过时才发现.
- **"可能panic"的子句有两种写法**: `P ==> may_panic()`和vostd `0195b8176`起的`allowed_to_panic_if(P)`. 只认第一种时, 新提交上没有一个client假定not P, 65处的断言全部失败, 在判定时被当成了噪音. 现在两者都认 (也认嵌套在`==>`之下的).
- **断言`!P`而不是假定它**, 使每个走到`read_once`, `fill`, `split`的client都失败在panic子句上, 之后的事实都量不到; 改为`assume(!P)`后162个client由失败变为通过.
- **私有字段不能出现在公开函数的ensures中**; **闭包的规格只经`call_ensures`转发**; **trait的默认ensures不适用于覆盖它的实现**.
- **Verus的版本跟着vostd走**, vostd不固定它; 新提交可能要新的Verus. 原版ostd必须先0 errors.

## C. VIR和抽取

### C.1 VIR丢了的, 抽取时补

- VIR抹去引用的生命周期, 自动取引用/解引用, 有界整数的扩展, trait实现的方法的requires, `Tracked`的位置. **每补一项都要重抽全部表逐条看差异**: 第一次补`Tracked`时对所有读取都加, 使75个通过的client编译不过.
- **`Tracked<T>`类型的参数** (proof函数中, 不是`Tracked(x): Tracked<T>`的绑定) 在元组中不要再包; 对`Tracked`字段做`is Some`要取`@`. 这两处错误使12个引理和`node::lock`编译不过.
- 源码中显式的`&p` (p不是引用) 在VIR中是借用p的临时位置: 要保留为`&p`, 否则被调用者得到值.

### C.2 由VIR写回Rust (每条都是一个编译错误)

- 经不经trait (`<T as Tr>::f`) 按VIR的trait列表判定, **不按路径倒数第二段是否大写** (`vstd::set::Set::empty`是结构体的函数). 数据类型的函数写`Set::<T>::empty()`, 不是`Set::empty::<T>()` (E0107).
- 元组结构体的构造写`PageTableOwner(x)`, 不写`PageTableOwner::PageTableOwner(x)` (E0599).
- `arrow_N`访问函数写回`x->0`; 经trait路径调用时要`&x` (E0308). 字段访问在`->`之后加括号: `(x->0).0`, 否则`x->0.0`读作浮点数.
- trait有类型实参时写`<Self as Trait<..>>::f` (E0284, E0107); 方法自己的无参数提及的类型参数要写出 (E0282); spec函数结果的类型参数无人决定时绑定写出类型 (E0283).
- proof函数的结果是spec值时不能`let tracked`, 要`let ghost mut r = arbitrary(); proof { r = f(..); }`.
- **Verus生成的项不是API.** Verus `5ef50d52`为派生的`Clone`生成`vdis%N%clone_clause_autoderived%`; 名字去掉命名空间后仍含`%`的不进表. 它们进表时是解析错误, 使整个模块的探针编译不过, 修补轮次用在一个一个地去掉它们上, `mm.page_prop` 152个条目全部`not-verified`.
- **关联常量.** vostd `4676a774b`后子句中的常量可以是impl的关联常量 (`ostd::mm::page_prop::impl&%26::AVAIL1_SPEC`), 直接写是解析错误 (同上, 整个模块); 要经self类型写 (`PageFlags::AVAIL1_SPEC`). trait的关联常量在VIR中是**没有实参的调用** (`NR_LEVELS()`, 以前确实是函数): 被调用者的`item_kind`是`Const`时不加`()` (E0618).
- **VIR的路径格式随Verus变.** Verus `84ae63ed`起每段带命名空间 (`t%mm`, `tdis<N>%NAME`, `vdis<N>%NAME`). 换Verus后先看VIR打印代码 (`ast.rs`, `printer.rs`) 的diff.

### C.3 名字解析

- **表中类型写最后一段, 由client的import解析**: ostd的全路径常经过私有模块. ostd的**trait**以前写定义处的路径 (`crate::sync::rcu::non_null::NonNullPtr`), vostd `eb1a9d044`把`sync::rcu`改为私有后E0603, 而rustc对限定路径中的trait**不给**经重新导出的建议, 修补无从下手. 现在也写名字 (135个trait名互不相同).
- **同名类型** (vstd的`simple_pptr::PointsTo`, `pcell_maybe_uninit::PointsTo`, vstd_extra的`array_ptr::PointsTo`) 解析错 (E0107): ostd和标准库以外的同名类型带上模块. ostd内部的冲突目前没有实例, 出现时要改抽取器.
- **trait方法的self类型有同名固有方法** (`<Frame<M> as NonNullPtr>::into_raw`与`Frame::into_raw`): 方法调用解析到固有方法, 探针报requires-weaker. 曾经为此给表加了固有方法的requires, **那是把表加强了**, 而探针查不出; 后来抽取器改对, 手修的覆盖表反而错了, 两个client由verified变failed, 要追到表的层才找到. 正确的做法是写成`<Self as Trait>::name`.
- 关联类型: trait有类型实参时写`<M as Repr<MetaSlotStorage>>::ReprPerm`; `M::ReprPerm`在M有两个`Repr<..>`约束时有歧义 (E0221).

### C.4 源码一侧

- **item-index的旧构建不认`--full-spans`**, 前身悄悄地使每条子句退回VIR的写法 (环境中对齐数为0, 一直没发现). 现在抽取时拒绝这样的输出.
- **在声明了client模块的检出上导出VIR**, 模块文件多一行声明, 其后的跨度都偏一行. 导出前确认检出干净; 由跨度找源码时取起点附近最近的`fn NAME`.
- **`#[verus_spec(..)]`中有`#[trigger]`**: 把以`#[`开头的行一律当作属性开头会在那里截断; 要数括号.
- 不在`verus!`中声明的枚举没有`->` (`util::either::Either`); 表和`knowledge`都看不出, claim要用`matches`.
- 扫描的模块正则要带`ostd::`前缀 (`^ostd::(mm|sync)(::|$)`), `pub(crate)`在VIR中写作`ostd::`; 写错重扫了两次.

### C.5 版本之间

- **impl的编号随提交变** (`impl&%5::from_unused` → `impl&%7`), 知识, 证人, 判定, 修改都按这个名字记. `rename-by-key`早就有, 但workflow中没有一步运行它 (2026-11-22补上).
- **源码的键也会变**: self类型的泛型实参变了 (`VmSpace<'a>` → `VmSpace`, `Cursor<'rcu, C, A>` → `Cursor<'rcu, C>`), 65个旧名字中32个因此找不到. 退一步用去掉泛型实参的键, 只在新旧都唯一时采用.
- **更新后没有一步算新提交的规格指纹**, `knowledge`报`no-digests`, 不能`--accept`.
- 测试按impl编号引用真实表中的API, 换提交后测试失败而表是对的; 测试要按源码的键查.

## D. 生成和良构性

### D.1 规则过宽 (无声地丢client)

- **第一版生命周期规则**一律禁止借用局部值, 悄悄丢了rwlock, mutex, spin的几百条通过的链, 总数上几乎看不出.
- **共享引用一律算借用**: `get_lock(guard: &MutexGuard<'a, T>) -> &'a Mutex<T>`的结果随guard的drop失效, "drop之后再加锁"写不出. 要按源码的生命周期算借用流 (`no-flow`).
- **借用者活着时一律拒绝规格中使用**: 而"活着"只是"没失效", rustc (NLL) 接受借用者以后不再用的程序; 一律拒绝悄悄略去了重述requires的断言.
- **按"有一条被绑的子句就丢client"**, 丢了`split`的`self.inv()`这样的好事实 (同一client中另一条子句把新offset和产生的段绑在一起). 改为每条都被绑才丢.
- **flow中所有执行参数都不生成** (第一版), 删掉了5个本来通过的segment client: `split(offset)`中offset正是调用者的选择.

### D.2 规则不够 (有声的, 但要找原因)

- `if-let`取出的值没有继承借用: `cursor_mut_at(&mut list)`的`Some`中的游标在链表再被借用后照样能用, 生成了E0499.
- 共享借用没有使可变借用者失效: `VmWriter::from(slice)`之后`VmReader::from(&*slice)`, 写者再用是E0502.
- 约束提到`'a`时 (`get<'a>(&'a self) where P: NonNullPtrRef<'a>`), 约束落在client的`'a`上, 不能借用函数体中的值 (E0597), 也不能取`'_`. 真实调用者写高阶约束`for<'b>`; 一律渲染成高阶的试过, `L::RefPermission`这样的简写对它有歧义 (E0212). 现在判为不良构.
- client的共享引用参数写成`&G`时, API要`cursor(&'a self, guard: &'a G)`同样长是E0621; 写成`&'a T`.
- goal新构造的client复制探针参数时没带生命周期参数 (E0261).
- claim文本用了约束更多的impl才有的spec方法 (`DmaStreamSlice::inv`要`M: OwnerOf`), claim client没有这个约束 (E0599). 写claim时只用API自己的impl能用的函数.
- claim绑定的`forall|r|`被代入的结果变量`r`捕获, 意思全变. 代入前先改名.

### D.3 选错了值 (编译通过, 但只会因此失败的噪音)

- **整数按VIR的类型流**: VIR把`Paddr`, `Vaddr`, `usize`都写成`usize`, 虚拟地址被给了lemma的`pa: Paddr`, 结束地址给了大小. 要源码中两边是同一个非裸整数类型.
- **同类型含义不同**: `alloc_if_none`返回的**子节点**的guard被当作父节点的guard (证否发现的).
- **知识中一个参数有两个角色** (两轮知识合并留下的), 枚举对API参数取第一个, 对client参数取最后一个, 哪个值都配不上. 现在有一个相同就算相容.
- **goal_err按类型配对**: `read_once(reader, owner)`出错后, `write(writer, reader, owner_w, owner_r)`的`owner_w`配了reader的owner, 必然失败. 按角色配.
- **flow中F的owner配G的新对象**; **一个owner配给两个对象**; 协议**先取新参数**而不是前面调用产生的对象 (74组协议失败中60组). 分别由按来源配对, "一个owner只描述一个对象", `prefer-produced`处理.
- **tracked的`Option`给`None`**, 代入后某条requires为假, 被提升为client的requires, 后面的路径空洞 (vm_space 26个client). 要求藏在spec函数中时文本看不出, 由探针判定.
- **新参数的子句不提升**, 约245个client必然失败在"新参数从没被说成合法". 提升时第一版放宽为"没有被`&mut`借用或移走": `paddr`先给了`from_unused`再给`inc_frame_ref_count`, 入口就假定了槽在用, 替client回答了问题, 还使成功分支空洞 (12条新的空洞路径). 按值复制也算用过.

### D.4 目标回归的判定

- **触动的过滤用错了分支**: G不在H的结果上分支时只能用H的无条件ensures, 按Some的守卫算漏了失败. 分支由client的结构定.
- **出错之后不能过滤**: H在Err时什么都不改, 而G仍失败 (H的前提与G的相反). 过滤会丢事实.
- **P没有ensures** (external, trait函数) 时两步链永不相关; 简单地"没有ensures就算相关"重现爆炸 (page_prop 462 → 852). 要经由G推出条件.
- **共享变量的对应写成了嵌套循环**, `current_meta`被判为无干扰, 丢了两条事实. 这些错误都由**离线**与旧结果逐个比较发现, 没有跑Verus.
- **"每个G至多取6对"截掉了vm_space的链, "每个P只取第一个F"丢了kspace的** (第一个不是`clone`). 按个数截断会丢唯一的路径, 要按规则.
- **只看类型的往返**生成了大半不是往返的client; 要求两边的ensures都有连结果和实参的等式.
- **第一版goal直接写成多步产生者闭包**: page_prop 4158个 (`PageFlags`的运算互为产生者), 而cursor和sync是0个 (漏了"同一对象上先后的操作"这类依赖).
- **claim和assume压平成文本**, 切片器看不到其中的变量, 把产生`r`, `paddr`的调用切掉, claim切片全部编译不过. 规格要保留为模板或树.

### D.5 生成的时间

- **实参组合先造全积再过滤**: 并入8–13次调用的协议后, vm_space的生成32秒 → 54分钟. 逐个参数构造 (`canonical-combos`) → 7分钟.
- **不该在这一步调用的API也被全部展开再由性质判死**, 每多一次调用翻一倍. 改成惰性流, 先算else分支都试过, 没有加速; 展开前先由只看名字的性质判断 (`properties-may-call?`) → 78秒.
- **一个协议允许中间插入任意调用时耗尽内存; 参数取探针参数的并时mm.io有50万个client.** 协议要有上限.
- 仍未解决: 长协议中被接受的调用在`max-choices`的循环中反复展开 (每两次调用约翻一倍).

## E. 渲染, 运行和导入

### E.1 兄弟模块的导入 (第一次从零重做时由探针的编译错误发现)

- 不能`use super::*`: 那是父模块的项, 与模块的同名 (vm_space的`Cursor`与page_table的, E0659).
- 模块之内它自己的定义胜过一切glob, 兄弟中模块的项也是glob, 与模块自己的glob导入相撞; 要显式导入模块声明的非私有类型 (显式胜过glob).
- 模块自己已导入的名字表不再导入 (E0252); 经私有子模块的`use`不取; `use self::`改经模块; `#[cfg]`之后的不取.
- 自由函数写绝对路径, 不写`super::f` (只在模块之内对).
- 一个模块的表并入别的模块时只取条目不取导入 (导入相对于那个模块的位置).
- **私有子模块的glob导入**: 协议的`use crate::mm::page_table::cursor::*;`在兄弟中是E0603, 整个模块编译不过 (第一次全部模块的运行中mm.dma, mm.page_table, node因此没有结果). 由rustc报出的那行在下一轮去掉.
- **经client模块本身的导入建议** (`use crate::mm::page_table::cs_clients::array_ptr::ArrayPtr;`) 只在那个模块成立, 表却被别的模块用, 一次整个cursor模块编译不过. 改写为经client自己的那条导入, 没有就不采用.

### E.2 导入轮次

- **只做一轮不够**: rustc分阶段报错, 名字都解析了才报方法所属的trait不在作用域; `rwarc`的4个协议client停在`deref`上. 至多3轮.
- **一行显式导入会遮蔽glob导入的同名项**, 可能改变别的client: 所以整模块重跑, 通过的不减少才采用.
- 曾试过读别的模块顶层的`use`改成绝对路径: 要自己解析`super::`, `self::`, `mod.rs`的相对路径, `cfg`, 全取又撞私有导入 (E0603) 和同名 (E0252). 不用.

### E.3 续跑的键

- 键只含生成的client, 不含**展开后的client**时: 修了两个client的`&`之后续跑, 模块没重跑, 编译错误照旧, 总数上看不出.
- 只看client和检出时, 改了修补或渲染之后续跑会悄悄沿用旧结果.
- **导入轮次和崩溃拆分在evaluate.rkt中, 不在键里**: 改了E0603的规则, 结果变而键不变, 要手工删`key.sha`. 移到`module-run.rkt`并进键.
- 反过来: 给client加了一个只供报告用的标签 (`(plan SHAPE)`), client文件变了, 键也变了, 多重跑了7个模块.
- 打了补丁的运行若键不含检出的改动, 会重用没打补丁时的结果.
- 每次运行结束 (包括出错时) 删去client模块, 还原模块声明, 恢复`Cargo.lock`.

## F. 分组, 分析和确认

### F.1 分组和回归

- **按文本分组**: 同一子句因变量名不同 (`self_g`, `x0`) 分成几组, r23有1475组; 按身份807组.
- **证人的期望是渲染文本的正则**: 渲染一改 (`(*reader).inv()` → `reader.inv()`), 两个问题被误报为gone. 改为只按子句的身份.
- **已知问题只在证人失败处挂标签**: claim证人与goal client是同一个缺的事实, 子句不同, 组上没有标签 (N5). 按"主体调用位置上的事实"挂.
- **知识标签用client中任何API的条目**会标注几乎一切, 掩盖候选; 只用关于失败的那个API的.

### F.2 分析命令的接口

- `refute`解构`(at CLIENT ID)`, 而`groups`已改为写`(at CLIENT ID CULPRIT)`, 在第一个模块就停.
- 表中`(source none)`被当作字段列表读, `provable`停下.
- **`provable`续跑时重新按当前标签选组**: 写下判定后组少了, `groups`又把证出的组排前面, 什么都没改也因候选次序变了而拒绝续跑. 现在第一次就记下所选的组, 候选按集合比较.
- `fixes`文件中`(no-fix ..)`的形式使读取停下.

### F.3 确认的归属

- **`confirm`中原有证明的失败**: 第一版规则是"归给它调用的函数的子句", 理由写成"`fill`调用`write_val`", 对照VIR**它并不调用**, 规则归不到, 槽又停下. 真正的联系是**同一模块** (一个求解器, 查询变了会扰动脆弱的证明). 写原理之前要对照VIR核实.
- **`breaks-proof`只到模块**: 一处segment的证明失败, segment.rs上7个修改一起被去掉, 其中有单独成立的. 被去掉的逐个再试.
- **相关的修改分在不同槽**, 上层转发下层新给的事实的修改单独永远证不出, 不是它的错 (4个). 加`with`.
- **`AFTER`数重跑中这组的client**: 原来的client改为超时就不进任何组, 组降到0算作清除. R17多确认的一组就是这样, 第七次时超时消失, 又在这条子句失败. 要数这组原来的client, 超时算未清除.
- **每次重新分槽验证已确认的修改** (108个中90个早已确认, 28次验证), 新修改还能**替换**已确认的, 替换不成立时连确认一起丢, 只好撤回再跑 (第三, 五, 七次). 已确认的冻结为基线, 不可替换.
- **修改经open的spec函数加强了`external_body`的契约** (R50): 是不经证明地加强可信代码, 工具查不出. 写修改时禁止, 判定时要看.
- 修改带`#[verifier::loop_isolation(false)]`, 函数体中有`assume`: 不是纯规格的改动, 要标出.
- **一起证出不等于单独成立**: provable中一个F加几条时互相帮助; 要分槽逐条确认.
- 重跑中由通过变为失败的若是rlimit, 是修改的代价 (更多事实使长证明变慢), 不判定.
- **并行验证的副本不能共用cargo目标目录** (锁, 增量产物).
- **补丁文件要核对内容再用**: 一次shell命令出错使"合并后的补丁"没有替换旧的, 报告按合并后的写了, 打补丁评估只覆盖了一半. 用前`git apply --stat`与报告对照.

## G. 流程和度量上的教训

- **逐个client比较, 不看总数.** 两次运行按client名比较状态, 每个变化都要解释; 名字中的哈希不只由调用序列决定, 改名而状态相同的按调用序列对上.
- **通过的变多不等于更好.** 协议全用新参数时, 新参数的requires被提升, 什么也没检验却"通过" (`sync.rcu`的协议16/16); 改成接着用前面的结果后通过变少, 暴露出下一层的问题.
- **一次只改一层, 改完就比较.** 同时换提交, 改工具, 改知识, 变化无法归因.
- **基线必须是当前工具跑出的.** 存档的探针早于一次抽取的修改, 550个not-verified和218个vacuous都是旧工具的误判; 那次修改的bug也因此一直没暴露.
- **手修的覆盖表会过时且变错**: 它随`base`换提交, 内容不随源码更新. 现在没有手写的覆盖表.
- **不继承上一轮的成果代价最大**: 重写知识只得到上一轮的六成, 72个API丢了全部claim. 知识, 判定, 已知问题都要作为数据移植.
- **回归要在一开始做**: 一轮评估曾重新发现一部分已知问题, 漏掉其余的. 现在是一条命令, 每轮必跑.
- **分几波审会反复返工**: r1中`fixes`跑了7次, 3次是撤回. 一次审完, 一次修改, 一次修补.
- **判定一组要读组里的每个client**: 组按第一个失败的子句分, 真实的调用者可能在`noise`组里, 缺自己requires的client可能在`defect`组里. r1中逐个检查的893个失败client里约310个是client自己的错.
- **知识说"不是缺陷"时责任者其实证得出** (5组): 知识只是标签, 不是判定.
- **workflow缺一步时不临时变通**: rename-by-key和新提交的指纹都是"工具有, 流程没跑"; 发现后先改workflow.md再做.
