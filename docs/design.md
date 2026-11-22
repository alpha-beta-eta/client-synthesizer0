# client-synthesizer0的设计

本文档讲client合成器本身: 它做什么, 按什么原则设计, 由原则得出的取舍, 实现时必须注意的事项, 以及目前的缺陷. 怎样用它评估规格见前身的[evaluation.md](../../vostd-client-synthesizer/docs/evaluation.md) (流程不变; 本版的差别在[README](../README.md)的"与前身相比").

本版由前身 ([vostd-client-synthesizer](https://github.com/alpha-beta-eta/vostd-client-synthesizer), 本机上是`../vostd-client-synthesizer`) 整理而来, 本文档也由前身的design.md改写: 保留的部分照旧, 改了的部分 (3.2, 3.6, 3.7, 3.8, 3.10, 3.11) 写现在的做法和取舍, 去掉的部分 (族, 后条件合成, 引理重试, 手写的覆盖表) 不再描述. 文中"enumeration.md", "triage.md", "representation.md", "time-sinks.md"都指前身的`docs/`中的文件, 那里有每个决定的测量. 数据目录按惯例写作`data/`.

## 1. 问题

在Verus中, 调用者对一次调用的结果所知道的, 只有被调用函数的requires和ensures. 规格可能不够用: 缺ensures, 没有转发下层已经证明的事实, 没有框架条件, 签名拿走了调用者还需要的tracked资源. 这时函数本身照样验证通过, 问题要等到有人按真实用法写调用者时才暴露. vostd (Asterinas的Verus版本) 中大多数API还没有已验证的调用者.

规格也可能不可信: 被Verus信任而不检查的代码 (`assume`, `admit`, `external_body`, 公理) 若说得比实际行为多, 依赖它的已验证结论就可能不成立.

client合成器生成调用vostd API的已验证调用者 (client): 调用API, 再调用下一个, 或断言调用者需要的性质, 在vostd中由Verus验证, 把每个错误归到client的具体语句和子句上. 证不下去的地方是规格缺陷的候选; 补上建议的修改后client能证过, 被修改的模块和整个crate仍能验证, 就确认了缺陷和修法. 合成器不判定缺陷, 只产出事实.

## 2. 设计原则

**原则1: 先生成程序的表示, 再生成程序.** client, API表, 调用知识, 检查结果, 运行结果都是S表达式; 只有渲染一步知道Verus的写法. 从源码原样复制, 无法结构化的片段 (类型, 规格子句) 是不透明结点`(src "..")`, 对它们的变换集中在一个有明确规则的函数里. 每次运行的表示存档 (`plan.rktd`), 出问题时先看表示, 再看渲染. 不做格式化.

**原则2: 工具只产出事实, 判定由人或LLM做; 人或LLM写的东西必须机械地核对.** 事实是: 哪个client的哪条语句, 哪条子句失败, 哪条路径空洞, 哪个候选证得出. "是不是缺陷"是判断. 反过来, 判断者写下的东西 (API表, 手加的requires, 期望, 调用知识, 修改) 都可能错, 不经核对就会悄悄地使结论失效: 表由探针核对, 路径由空洞性检查核对, 修改由整个crate的验证核对, 知识只当作假设或标签.

**原则3: 便宜的良构性由合成器保证.** 能简单机械地保证的 (作用域, 模式, 类型匹配, 所有权和借用的近似, 资源的关闭), 以及不保证就会使大部分生成的程序编译不过的, 由合成器在生成时保证; 其余交给rustc和Verus. 签名上的问题 (按值拿走tracked资源) 因此成为表示层面的事实, 不会走到编译.

**原则4: client模仿真实调用者.** 实参只来自client的参数和前面调用的产物, 不凭空引入值; 资源按协议在调用之间传递 (权限为被操作的对象取; 读者的owner不传给写者); client的requires由它的第一批调用推出, 不为了通过而手加. 不像真实调用者的client, 其失败只说明client写错了, 是噪音.

**原则5: 每个结论可复现, 可归因, 可信.** 结果绑定在vostd提交和Verus版本上; 每个错误带语句编号, 渲染出的那一行和被调用者的源码行; 每个模块有必定失败的sanity断言, 每条路径末尾有必定失败的空洞性断言; 名字由内容决定, 换版本时可以逐个对比; 不需要Verus也不需要vostd数据的部分 (规格文本, 知识的漂移, 可信代码的列举和判定的核对) 由golden测试固定.

绑定到版本对不同的数据要求不同, 按"过时了会怎样"决定:

- **API表必须与检出同步, 由合成器强制.** 表过时, client按旧签名和旧requires生成, 结果误导; 而表的requires比源码强时探针发现不了 (3.2). 所以每张表记它对应的提交, 不一致时一切运行都被拒绝.
- **调用知识可以落后, 但必须如实记录它核对时的提交.** 知识只用来生成假设 (claim, protocol) 和标签 (3.7); 过时的知识使种子和标签变弱, 不会使"通过"变得不可信. 漂移的报告是提示, 不阻止运行.

**原则6: 规模服从用途.** 枚举是为了发现问题, 不是为了覆盖空间. 调用序列的数目由分支和实参选择决定, 不由深度决定, 指数地增长; 每一族client都要有预算 (深度, 每步的延续数, 每族的上限), 超出时降级而不是耗尽内存. 代表一种用法的client (真实的调用序列) 只要几个忠实的实例.

**原则7: 关于API的知识是数据, 不是代码.** API表, 往返关系, 调用知识 (角色, 协议, 注释的声称, 可假定的事实, 已知的限制) 都是带出处的数据文件, 可以由LLM起草, 由人核对, 由机械检查. 合成器的代码不含关于某个模块的知识.

**原则8: 尽可能简单.** 同一件事只在一处做; 新的调用形式复用已有的机制 (调用是事件, 性质是事件上的文法, 良构性逐步检查).

**原则9: 漂移是分层的, 每层有自己的核对.** 换vostd或Verus时会变的有: 工具链 (Verus本身), 中间格式 (VIR), API表, 调用知识, 生成器的隐含假设 (新的API形状碰上平时不显的近似), 以及已有的结论. 每层的毛病在本层不报错, 在下游以别的样子出现: VIR的格式变了, 表现为大批条目抽不出; 抽取的bug, 表现为一批同类的条目编译不过; 知识过时, 表现为claim编译不过或空洞地通过. 所以每层要有能出错的核对 (表: 探针和版本; 知识: 名字, 良构, 锚, 指纹; 生成器: 逐个client的比较), 不能只看最后的通过数. 汇总数字会掩盖 (4.6).

**原则10: 稳定和机械.** 从删掉全部数据的状态重新做 (抽取API表, 探针, 生成, 运行, 分组) 到最终结论, 耗时和结论都不应有夸张的差异; 为此中间环节不能大量依赖LLM审阅之后的修补. 中间环节可以用LLM, 但它不应占大部分的时间和工作: 若一轮评估中95%的时间是LLM在读结果, 改表, 修证人, 工具就没有意义了. LLM和人的主要工作在两头: 起草知识 (原则7, 它们由机械检查核对), 判定和确认缺陷 (原则2). 中间每一处人工修补都是重做时的漂移来源 (手修的覆盖表, 为某个条目改的证人, 手选的模块和深度), 要尽量换成由原则推出的机械规则; 换不掉的, 要能由数据重放, 并写明它的理由. 推论: 表示和规则要有原则 (源码和VIR按跨度对齐, 而不是按名字猜, representation.md 10); 枚举要有依据 (只生成能回答一个问题的client, 3.6), 而不是先多生成再靠人筛.

## 3. 由原则得出的取舍

### 3.1 表示 (原则1, 7)

表由VIR和源码 (item-index, verus_syn) 一起抽取: 名字解析, 模式, 签名取VIR; 子句的写法, 生命周期, 借用, ensures, 数据类型取源码. 改动的经过和还没做的见`representation.md` (第9节是现状).

- **类型**用紧凑的S表达式: 符号, `(& T)`, `(&mut T)`, `(assoc T NAME [TRAIT])`, `(tuple T ..)`, `(NAME T ..)`, 生命周期`|'a|`. 类型的比较是单向匹配: 被调用API的类型参数可以绑定, client的类型参数固定.
- **API表**每个API一个条目: 模式 (exec/proof/spec), 调用写法 (方法或函数路径, 路径中需要实例的类型参数), 泛型及约束, 参数 (模式和类型, 接收者叫`self`), ghost参数及其写法 (`with`或尾随的`Tracked`), 返回值, 幽灵返回值, requires (规格AST), 以及模块级的`uses`. 覆盖表 (`base`加上改过的条目) 描述修改后的签名或人工的修补.
- **规格表达式**是小的AST (调用, 字段, `old`, 比较, 算术, 逻辑, `is`, 元组, `as`, 解引用和借用), 加上不透明的`src`. 同一棵树按上下文渲染: client的requires中`&mut`参数写`old(x)`, 函数体中写`*x`.
- **client**是参数和语句: 绑定一个调用, ghost快照, 断言, 断言某个调用的requires (逐条子句), `if-let`/`if`的树, 有界循环. 调用中ghost参数显式给出.
- **结果的结构** (representation.md C2): 返回元组的调用之后立即解开 (`untuple`, 渲染为`let (mut p, Tracked(perm)) = v;`), 分量各自成为变量, 像真实调用者那样分别传给后面的调用 (`into_raw`的指针和权限给`from_raw`). 每个分量的模式 (exec, tracked, ghost) 取自源码的返回类型 (`(NonNull<..>, Tracked<..>)`): 表中的类型去掉了`Tracked`; 没有源码的条目不解开. `Result`的`else`分支可以绑定`Err`的载荷 (渲染为`match`), 只在载荷的类型是某个被枚举的API的参数类型时 (`UniqueFrame::try_from`的`Err(frame)`把frame还回来, 之后还能用); 一律绑定只会改写所有client的渲染, 而`Error`没有人接. 分量是体中持有的值: 传给引用参数, 而这个引用的生命周期 (源码中的) 是约束所指的 (`borrow_perm_as_ref_perm(tracked perm: &'a ..)`, `L: NonNullPtrRef<'a>`) 时, 要活得和client的`'a`一样长, 不良构 (E0597).
- **结果**: 每个client一个状态 (verified, failed, compile-error, ill-formed, not-verified), 错误 (语句编号, 消息, 渲染的行, 被调用者的requires所在), 空洞的路径.

### 3.2 API表从哪里来 (原则2, 7)

- 由VIR抽取: 模式, 泛型, 参数, 返回值, requires都在VIR中; `#[verus_spec(with ..)]`的ghost参数由`_VERUS_VERIFIED_`版本与普通版本的差得出; 没有`self`的关联函数的自身类型由源码解析器补.
- 取哪些函数: `pub`的, 以及可见范围超出所属模块的 (`pub(crate)`, `pub(super)`, `pub(in crate::mm)`): 它们在别的模块中有调用者, 而client模块是所属模块的兄弟 (3.8), 都能调用. 私有的 (只在所属模块中可见) 是辅助函数, 不取.
- 抽取同时决定每个模块的client放在哪里 (target, 3.8), 并把这个位置要的导入写进表的`uses`.
- trait的默认方法在impl上的继承实例也在表中 (enumeration.md 14): 它们在impl上可能不可调用 (VmIo的`obeys_*`在前条件上), 探针的`vacuous requires`就是这件事的smoke test.
- VIR丢掉了一些东西, 抽取时补回: 共享引用传给取值的参数时的`*`, 值传给取引用的参数时的`&` (包括Rust的自动取引用), 有界整数到`int`的扩展, trait实现中方法的requires (取trait声明的, 换参数名和`Self`), 声明中`Tracked<T>`参数在元组中的包装, 生命周期 (近似: 一个签名中带生命周期的类型共用一个`'a`; 引用自身的生命周期在渲染时取所指类型的第一个生命周期实参).
- 翻译不了的子句 (量词, 块, `match`): requires的保留为源码文本的模板, 参数的自由使用是洞 (`lib/model/template.rkt`; 2026-11-12以前略去, 条目被判为requires-weaker; representation.md 6.8); ensures的略去. 签名写不出的函数 (闭包参数) 略去并记录原因.
- lemma (只有spec参数, 没有结果的proof函数) 带ensures并标`(lemma)`: 探针核对它们.
- 源码一侧由item-index (verus_syn) 给出, 子句与VIR按跨度对齐 (representation.md 10). item-index的旧构建不认`--full-spans`, 会悄悄地使每条子句退回VIR的写法 (2026-11-16, 环境中的旧构建使对齐数为0, 前身没有发现): 抽取时拒绝这样的输出.
- 抽出的表**必须由探针核对**: 每个条目一个client, 参数与声明完全相同, 于是条目的requires被提升为它的假定, 体是一次调用. 编译错误说明签名不对, 前提失败说明表的requires比源码弱, 空洞说明requires矛盾. 表的requires比源码强时发现不了, 所以只抄不改.
- 修补只有机械的一层 (`fixes/`): 采用rustc的建议 (单一的import, 缺的约束, `'static`), 再经探针. 只用探针为`ok`的条目. 没有手写的覆盖表: 前身的`manual/`最后只剩"哪些guard必须关闭"一项 (3.3), 它是关于API的判断, 现在是调用知识 (3.7); 而手修的覆盖表随`base`换提交, 内容却不随源码更新 (time-sinks C13), 是重做时漂移的来源 (原则10).
- 探针的`vacuous`分两种原因, 由去掉调用的变体分开 (变体的requires写明提升出的那些): 变体也空洞, 是声明的requires互相矛盾 (`vacuous requires`); 变体不空洞, 是调用之后才矛盾 (`vacuous after-call`: 源码的ensures在这些requires下推出false, requires实际上不可满足, 或可信代码过强). 两者都要读源码判定, 后者不能直接当作表写错.
- **表绑定在提交上** (原则5). 抽取时每张表写入`(at "COMMIT")`, 即导出VIR的检出的提交; 覆盖表 (`fixes/`) 随它的`base`. 运行 (`run`, 以及建在它上面的探针和评估) 先比较表的提交与检出的HEAD, 不一致就拒绝; 一张表由几个模块的表合成时, 每个都要一致. 有意对别的提交做试验时设`CS_ANY_COMMIT=1`, 那样的结果不作结论.

### 3.3 良构性检查 (原则3)

逐条语句检查, 停在第一处不良构, 给出语句编号和事实:

- 作用域: 变量已绑定, 未被移走, 借用未失效; 一个名字只绑定一次 (不模拟遮蔽, 遮蔽会使未关闭的资源悄悄消失).
- 模式: exec参数只接受exec变量, tracked参数只接受tracked变量, spec参数接受任何变量或规格表达式.
- 类型: 匹配, 且API的每个类型参数都由实参或显式的类型实参确定; 生命周期参数只取生命周期.
- 所有权: 按值传入非Copy的值即移走; 同一调用中被移走或`&mut`借用的变量不能再出现; 传递方式 (`x`, `&x`, `&*x`, `&mut x`) 由参数类型和变量类型决定, 记在计划中.
- 借用: 返回引用或结果类型带生命周期的调用, 借用那些生命周期能到达结果的引用参数 (由源码的生命周期按Rust的省略规则算出, 表中没有借到的记为`no-flow`, 共享引用和`&mut`都算; 2026-11-11以前只对`&mut`算, 共享引用一律算借用, 于是`get_lock(guard: &MutexGuard<'a, T>) -> &'a Mutex<T>`的结果随guard的drop而失效, 真实调用者"drop之后经get_lock得到的锁再加锁"写不出; 没有源码的条目仍一律借用); 被借的变量之后被移走或`&mut`借用时结果失效, 被共享地借用时可变地借用它的结果失效 (`VmWriter::from(slice)`之后`VmReader::from(&*slice)`, 写者不能再用: E0502); `if-let`取出的值借用着被取的值所借用的 (`cursor_mut_at(&mut list)`返回的`Option`中的`CursorMut`仍借用着链表; 原来取出的值没有借用, 链表再被借用后游标照样能用, 生成了E0499的client); 规格中使用一个变量与共享借用一样, 使可变地借用它的值失效, 之后再用那个值才是不良构的 (`self.wf(owner)`之后再用由`&mut self`得到的`CursorMut`: E0502). 原来是一律拒绝在借用者活着时的规格使用, 而这里的"活着"只是"没有失效", 不知道它以后用不用: rustc (NLL) 接受借用者以后不再用的程序, 一律拒绝因此丢掉了合法的断言 (重述requires的`assert-requires`被悄悄略去).
- 生命周期 (表中一个签名只有一个`'a`, 3.2): 调用中从不写生命周期, 由rustc推断, 所以一般不必管; 只有API的约束提到这个生命周期时 (`get<'a>(&'a self) where P: NonNullPtrRef<'a>`), 约束被提升为client的`P: NonNullPtrRef<'a>`, 落在client自己的`'a`上, 而它比函数体活得长, 于是不能借用函数体中持有的值 (局部变量, 以及按值传入的参数: E0597), 也不能取省略的`'_` (约束不能落在`'_`上). 两者都判为不良构. 真实调用者对泛型的`P`写的是高阶约束`for<'b> NonNullPtrRef<'b>`; 表写不出它 (把约束一律渲染成高阶的试过: `L::RefPermission`这样的简写对高阶约束有歧义, E0212), 所以在局部的guard上调用`get`做不到 (5.1).
- 必须关闭的类型 (没有`Drop`的guard) 在离开作用域前必须按值传出. 是哪些类型由人定 (抽取列出候选: 持有`Tracked`字段, 没有`Drop`), 写在调用知识中 (`(must-close TYPE (why ..))`, 3.7); 现在是6种锁的guard, 它们的`drop`要求锁的不变式已恢复. 试过的机械规则都与人的选择不一致: "有`drop(self)`的条目"也选中`Frame`, `Segment`, `RwArc`和RCU的读guard (真实调用者让它们隐式地drop), "`drop`有requires"漏掉`MutexGuard`和rwlock的写guard (它们的条件在类型不变式中). 所以它仍是判断, 只是从覆盖表移到了有出处, 受检查的知识中. 枚举在路径结束时若还有未关闭的值, 用表中只接收这个值的函数 (`drop`) 释放它, 而不是丢掉这条路径 (否则guard多在最后一步才拿到, 这些模块的client少八成).
- client的泛型约束不手写: 每次调用时并入API类型参数的约束实例.

不检查的: 具体类型上的trait约束, 规格表达式的类型 (除简单情形), 其余借用规则. 它们交给rustc.

良构性的规则拒绝得过宽是**无声的**: client从生成中消失, rustc和Verus都不会抱怨; 拒绝得不够是有声的 (编译错误). 所以规则要贴着真实的出错机制写, 不按"可能出错"写宽; 每次收紧之后与基线逐个client比较, 确认消失的只是原来编译不过的 (原型中第一版的生命周期规则一律禁止借用局部值, 悄悄丢了rwlock, mutex, spin的几百条通过的链, 总数上几乎看不出).

### 3.4 client的requires (原则4)

被调用API的每条requires子句, 代入实参后若只提到尚未动用 (未被移走或`&mut`借用) 的client参数, 就提升为client的requires; 其余是义务, 由Verus在调用处检查. 于是client的假定恰是"真实调用者在开始时必须满足的", 而后续调用的前提由前面调用的ensures负责. 提升不区分分支: 调用者不能选择走哪个分支, 必须满足每个分支的前提.

例外是参数的不变式: 后面的调用要一个已被动用的client参数满足`p.inv()`或`p.wf()`时, 它也作为入口的requires (`old(p).inv()`). 真实调用者一直持有它所传递的资源 (regions, owner) 的不变式; 不提升时, 每条中间调用对`p`什么也没说的路径 (如某个调用的`Err`分支) 都败在这里, 看起来是生成器的产物. 提升之后仍然失败, 说明中间那次取`&mut p`的调用没有保持它, 这是规格的问题. 只限于单个参数的无参谓词: 一般的子句在入口处的值上提升会使requires矛盾.

第二个例外是**还没用过的参数与已被动用的参数之间的子句**: 后面的调用G要一个新的client参数p与一个已被`&mut`动用的参数r有某种关系 (`p.wf(*regions)`, `p.relate_region(*regions)`, `p.inv_with(*owner)`), 而p此前没有被任何调用动用. 以前它不提升, 留作G处的义务, 于是client从头到尾没有说过p在开始时就是好的, 它在G处必然失败, 与前面的调用给了什么无关; 真实调用者手里的对象在开始时一定是合法的. 2026-11-17的r1中逐个检查的893个client里, 约310个是client自己的错, 其中约245个就是这一种, 集中在`goal_err` (219个中140个) 和`flow` (109个中66个). 所以这样的子句也提升: 子句中的变量都是client的参数, 都没有被移走, 没有被`&mut`借用过的都**还没有被任何调用当作实参用过** (按值复制也算用过), 至少有一个这样的, 被动用过的只是被`&mut`借用过 (先前的版本只要求"没有被`&mut`借用或移走": `goal_err`中`paddr`先给了`from_unused`, 再给`inc_frame_ref_count`, 入口就假定了这个槽在用, 替client回答了`from_unused`出错时的问题, 还使它成功的分支空洞; 2026-11-17比较时发现); 提升到requires中, 它说的是**入口时**的值 (render.rkt把`&mut`参数在requires中写成`old(x)`). G处的义务照旧断言, 问的于是是"前面的调用 (包括它出错的分支) 有没有保持关于p的事实", 即前面的调用的框架条件. 子句中有前面调用的结果 (局部变量) 的, 入口时还没有它, 不提升. 还有一个限制: **一个owner只描述一个对象.** client的requires中已经有同样形式的子句把这些被动用的参数与另一个对象联系起来时 (除去开头的接收者, 如`self_.0`与`self__g.pt_cursor.0`, 子句相同), 不提升: 生成器把同一个`owner`, `guards`配给了两个对象 (`flow`的两个链表, `goal_err`的两个cursor), 两条一起假定就互相矛盾, 路径空洞 (2026-11-17比较时: 7个client); 不提升时它们照旧在调用处失败, 判为噪音. **效果** (同一配置, 改前`out/r2-base`, 改后`out/r2-lift4`, 逐个client比较): 原来失败的41个通过 (40个`goal_err`; 逐个检查判为噪音的34个, 其余7个所在的组都是`noise`或`by-design`, 没有`defect`), 都不空洞; 27个仍失败的错误变了 (26个少了); 原来通过的都仍通过; 没有新的空洞路径; 1个多了整体的rlimit (requires多了). 逐个检查中约245个"新参数没有与状态联系"的噪音, 这一条只改变了49个 (34个通过, 15个问的变了): 其余196个的原因是**配对**, 不是提升 (`goal_err`给第二个调用配了新的owner而不是第一个调用用过的, 82个; 把一个对象的owner给了另一个对象, 59个) 和条件性的ensures (`from_user_space(ptr, len)`只在`ptr`满足条件时给`inv()`, 生成器没有选使条件成立的输入, 约55个). 前者要`goal`/`goal_err`/`flow`也按来源配对 (3.5的`pair-by-origin`, 现在只用于协议).

代入实参时类型要跟着变 (requires中, 以及spec实参): 被调用者按引用取的参数 (`*x`), client传的是值时写`x`; 被调用者按值取而client的变量是引用时写`*x` (`to_from_repr(r, perm)`中的`r: &mut MetaSlotStorage`; 元组中没有自动解引用, `(self.split(..) == (*self_, *self_))`); spec实参也一样 (`lemma_view_in_vaddr_range(&v0)`); 反过来, 被调用者的`&`参数写作spec函数的实参 (`DebugSpec::fmt_req(self, f)`, `self: &Self`), client传的是值时写`&r` (作为方法的接收者不必, 自动取引用).

被调用者的类型参数在子句中出现在名字里 (`<M1 as OwnerOf>::wf`, `size_of::<T>`, `Cursor::<C, G>::f`), 代入时按整个标识符换成调用的实例 (前面是`::`的不换: `Trait::M`是项); 2026-11-13以前只认`<`或`, `与`>`或`,`之间的, 子句改为源码的写法后`<M1 as ..>`漏换, 一个client编译不过 (representation.md 10.9).

手加的requires只在有理由时 (调用知识中的`assume`, 带出处), 并单独标出.

### 3.5 资源和协议 (原则4)

- tracked的`Option`参数可以给`None`, 但`None`代入requires后使某条子句为假, 或只在放弃某个条件P时成立 (化为`!P`) 时不给: 那样的子句被提升为client的requires, 使后面的路径空洞 (`get_slot`的`valid_frame_paddr(paddr) ==> slot_perm is Some`, enum.rkt的`none-forces?`). 要求写在spec函数之中时 (`raw_item_well_formed((.., Tracked(None)))`要`perm@ is Some`) 文本上看不出, 由探针判定: 对探针为ok的条目的每个tracked `Option`参数, 给它`None`, 去掉调用, 只留提升出的requires跑一次, 空洞就记`(none-vacuous API P)` (probe/中), 枚举不给这个`None` (2026-11-13: vm_space去掉了26个client, 在r22中全是空洞的).
- 缺少的tracked参数由提供者 (provider, 能从资源中取出ghost值的proof函数, 如`Option::tracked_unwrap`) 产生, 只在没有现成变量时; 提供者的spec参数只由当前调用的接收者形成: 权限为被操作的对象取.
- 同类型的tracked值有几个时, 按角色传参 (调用知识的`role`; 没有时, 以API另一个参数命名的变量不传给这个参数). flow也按角色共享: F的参数或结果与G的参数都有已知的角色而不同时 (`reader-owner`与`writer-owner`), 不共享.
- 对象和owner按来源配对 (枚举的`pair-by-origin`, 协议使用): 每个产生的值记下由哪个调用产生 (提供者取出的值继承来源). 一个调用得到调用k产生的对象时, 类型是k的幽灵返回值的类型的tracked参数也必须取自k; 反过来, 得到k产生的owner时, 类型是k的结果类型的exec参数也必须取自k. 真实调用者总是把对象和同一个调用返回的owner一起用; 交换或混用的client只会因此而失败. 没有满足的选择时不过滤.
- **goal_err和flow也按角色和来源配对** (2026-11-18). 以前只有协议 (枚举) 用这两条; goal_err (`after-err-client`) 按类型把H的参数配给G的第一个同类型参数, 不看角色: `read_once(reader, owner)`出错之后的`write(writer, reader, owner_w, owner_r)`, H的reader的owner配给了`owner_w`, writer却是新参数, `self__g.wf(*owner)`必然失败; flow中F的ghost结果 (owner) 流给G, 而G的对象是新参数 (`self_g.wf(gr)`), 只有F的ghost结果和F的结果可共享, F自己操作的对象 (F的`&mut`参数) 不在其中. 逐个检查中这两类约有140个噪音 (`goal_err` 82, 另一对象的owner 59). 现在: goal_err只把H的参数配给角色相容的G的参数 (都有角色时角色相同); flow中F的`&mut`执行参数 (F操作的对象) 也可共享给G, 只在G的requires把它与流过来的值联系起来时 (同F的结果); flow中G的新参数被G的requires与流过来的值联系起来时不生成这个client, 原来只对tracked的参数, 现在流过来的是F的ghost结果 (一个owner) 时也对执行的参数 (新的对象配F返回的owner); 流过来的是值时不: `split(offset)`的`offset <= self.size()`问的是为这个段选的偏移, 正是调用者所做的 (第一版对所有执行的参数都不生成, 删掉了5个本来通过的segment的flow client; 2026-11-18比较时发现). **效果** (改前`out/r2-lift4`, 改后`out/r2-pair2`, 逐个client比较): 原来通过的1503个都仍通过; 57个不再生成, 都是原来失败的, 所在的组都是`noise` (flow中新对象配F返回的owner; goal_err按角色配不上, 如`read_val`出错之后的`fill`); 26个的计划变了, 1个由失败变为通过 (`read_once`出错之后的`write`, reader的owner配给了`owner_r`). 配对正确之后goal_err的多数仍失败, 问的是前一个调用的框架条件 (`read_val`出错之后reader的视图, R1一类) 或混用fallible与infallible的API (fallible的调用没有owner), 不再是配错了owner. 与改提升规则之前 (`out/r2-base`) 相比: 失败的client 1486 → 1387, 通过的1462 → 1504.
- 新参数与产生的值不放在同一条requires中 (枚举的`consistent-fresh`, 协议使用). 按来源配对只管序列中某个调用产生的owner; 序列中没有调用产生它时 (`reference_count`的`slot_own`, 真实调用者从`regions`中取出), 前面调用产生的帧会配上一个新参数, 而API的一条requires把两者联系起来 (`x1.tracked_slot_perm@.value().wf(*slot_own)`): 对新参数一无所知, 这条子句必定证不出, client只会因此而失败. 所以一条requires子句 (代入实参后) 同时提到未动用的client参数和不是client参数的变量时, 这个选择被丢掉, 一个也不剩时这一步不走 (以前退回混用的选择, 生成的client只会因新owner而失败: `cursor_front_mut`不返回CursorOwner, 协议于是给后续调用一个无关的`owner_2`); 剩下的是一对一致的新参数 (什么也不检验, 但不是噪音) 或产生的值. 由来源的配对和这一条, 实参的选择是: 先用调用产生的值 (`prefer-produced`), 对象和owner同源, 不把产生的值与新参数拴在一起.
- 协议的类型参数是各调用探针的类型参数的并; 同名的类型参数取各调用的约束的并 (`RwLock::new`的`G`没有约束, guard的方法要`G: SpinGuardian`).
- 生命周期只在结果中的API (`SpinLock::lock`返回`SpinLockGuard<'a, ..>`) 在没有生命周期参数的client中 (从`new`出发的链) 实例化不了: 自由的生命周期参数只取client的生命周期参数. 取省略的`'_` (rustc推断) 是对的, 但使这类API处处可调用, `mm.dma.dma_coherent`的链由219个变为810个; 所以是枚举的选项`elided-lifetimes`, 默认关闭. 约束提到这个生命周期时不取`'_` (3.3).
- 性质约束调用序列: 事件是一次调用 (API名和"角色到变量"), 性质是事件上的文法 (正则加递归, 有交和补, 用Brzozowski导数求), 按对象切片 (每个帧, 帧和它的权限). 性质对每条路径成立 (协议) 或只对主路径成立 (挑选); 剩余文法确定为空时剪枝.

### 3.6 client的族 (原则2, 4, 6)

每一族问一个问题:

| 族 | 形状 | 问的问题 |
|---|---|---|
| probe | 在条目自己的前提下调用一次 (scan的一步, 不是评估的族) | 表是否忠实于源码; 方法是否可调用 |
| goal | 对每个API G的每条requires, 只放G的实参所依赖的调用, 再逐条断言G的requires. 依赖由一条有界的目标回归给出 (`lib/gen/families/goal.rkt`): R1产生 (A的输出是G的实参; 深度至多2; 两个实参各有产生者), R2修改 (H按`&mut`取G所取的值, 只在H可能改G读的东西时; H出错之后总是), R3再调用 (G按值拿走了实参, 再对产生者给的新值调用G), R4由ensures向前 (P的ensures写到的输出或`&mut`实参, 由读得最多的读者读一次), 往返 (由类型和ensures推出的恒等) | 真实调用者由这些调用得到G的实参之后, 能否满足G的每条requires; P说的东西有没有人用 |
| claim | 在API的前提下调用, 断言注释声称的性质 | 注释说了而规格没写的 |
| protocol | 真实调用者的调用序列, 主路径恰好按序调用 | 真实用法能否验证 |

取舍:

- 前身的repeat (能否再调用), flow (F的ensures给不给G需要的), chain (从F出发至多K步的序列) 都是goal的特例或超集: repeat是R3, flow是R1, chain中有用的序列是goal的计划, 其余是指数增长的冗余 (enumeration.md 7.1: r22的失败链切到依赖之后95.5%在同一处失败). goal每个client回答一个 (G, 子句, 依赖) 问题, 不需要按深度的预算和降级. 代价: 不在任何一条requires的依赖中的长序列不再生成; 真实的长序列由protocol (调用知识) 给出.
- 前身的post (由观察函数生成后条件的候选, 每个一次运行) 和lemma retry (在失败处按名字插入引理) 去掉了: 前者的候选少而难判定, "函数证得出却不导出"由drops和provable (3.9) 直接回答; 后者要回答的"缺规格还是缺调用者的证明", 由证否和provable回答.
- R1的client沿用前身flow的生成器 (`families/flow.rkt`, 名字以`flow_`开头): F先试共享tracked参数和幽灵返回值; G留作新参数的tracked参数若被G的requires与流过来的值联系起来 (`x.0.invariants(*owner_g, ..)`), 不生成 (同`consistent-fresh`).
- 结果的借用: 结果的类型带生命周期时, 检查器把它当作借用每个按引用传的实参. 表的`(no-flow P ..)` (由item-index按源码的生命周期得出) 列出借用到不了结果的`&mut`参数, 它们不算被结果借用.
- 每个调用前断言它的requires (逐条子句): Verus于是报告具体是哪条子句, 而不是笼统的"precondition not satisfied".
- 往返关系一部分由类型和ensures推出 (B取A的输出, 两次调用的ensures在结果和实参之间说的恒等), 一部分是声明的知识 (`identity.rktd`: 哪些spec函数标识一个值, 哪些往返要经同一个容器).

### 3.7 调用知识 (原则2, 7)

LLM从注释, 真实调用者 (vostd的调用点, 保留的ktest, Asterinas的内核和分配器) 和领域材料抽取每个模块的调用知识, 每条注明出处. 知识有两种用法, 严格区分:

- **当作假设去检验** (生成新的client): `claim` (注释声称的性质), `protocol` (真实的调用序列). 它们失败就是候选.
- **当作过滤或标签** (减少噪音): `role` (按角色传参), `assume` (真实调用者可假定的事实, 如引用计数不饱和; 作为client的requires: goal的种子调用的, protocol的种子调用的, claim所调用的API的, R1中G的只涉及client参数的 (换成G实际收到的实参; 涉及流过的值的不加, 它在入口不存在)), `prefer`, `limitation`, `not-defect` (只给失败加标签, 不删去任何client).
- **当作API的判断**: `must-close` (3.3, 哪些类型的值必须按值传出). 它改变生成 (枚举在路径末尾关闭这些值), 所以`knowledge`检查它所说的类型是模块的数据类型.
- 协议调用的API都要在某张表中, 否则是名字写错或条目丢了 (`protocol-outside`, 是问题). 例外是抽取按记下的原因留在表外的函数 (`left-out.rktd`: 闭包参数`closure-bound`, 写不出的类型): 那时协议不生成, 是表的表达力的限度, 不是知识的错, 记为注记`(protocol-left-out NAME (API REASON) ..)`, 模块仍是`ok`. 例: segment的7个协议从`Segment::from_unused`开始, 它的参数`metadata_fn: impl Fn(Paddr) -> (Paddr, M)`写不进表 (2026-11-16).

知识可能是错的 (注释说要"much heavier proof", 实际只要一条循环不变式). 所以它只能缩小或标注, 不能当作判定.

**知识与vostd的版本** (原则5, 9). 知识所依据的注释, 规格, 调用点都会变, 而大部分条目 (`role`, `assume`, `prefer`, `limitation`, `not-defect`的说明) 是文字, 不被编译或验证, 变了也不会报错. 所以每个知识文件记录它最后一次对照源码核对的状态, 由检查程序对照当前的检出报告漂移:

- `(at "COMMIT")`: 核对时的提交. 可以早于检出 (知识可以落后).
- `(spec-digests (API "HEX") ..)`: 核对时, 条目提到的每个API的规格指纹. 指纹取自**源码文本**: 函数上方的文档注释和属性 (含`#[verus_spec(..)]`), 签名, `requires`/`ensures`, trait实现的方法连同trait中的声明; 函数体不算. 不取自VIR, 因为VIR的打印随Verus变, 换一次Verus所有指纹都会变; VIR只用来找到函数. 指纹变了, 引用它的条目要重读.
- 出处带所引那一行的文字作锚 (`(comment "PATH:LINE" "TEXT")`): 行号移动时凭它找回那一行 (可以机械地改写行号), 找不到时那条知识失去了依据.
- 读过之后才记下新的提交和指纹 (`accept`); 不读就记下会让报告消失而知识没有核对.

能查出的: 所引的行变了或没了; 条目提到的API的规格 (含文档注释) 变了; API改了名 (impl重新编号: 名字检查报未知, 指纹按名字记, 重新编号后别的函数恰好得到旧名字的也会因指纹不同而报出). 查不出的: 条目依据的是API之外的东西 (claim中用到的别的spec函数, 类型的不变式, 调用者的代码) 变了, 由claim和协议的编译和验证发现, 其余靠人; 锚只说明"这一行没变", 不说明这一行支持这条知识 (初始化时按当时的行号取锚, 原来就引错的出处查不出, 除非那一行后来变了: 原型中一个协议把上游Asterinas的调用点记成了vostd的, 是在那一行的内容变了之后才发现的).

### 3.8 渲染和运行 (原则1, 5)

- 渲染: 每个调用和断言单独一行; exec的`let`一律`mut`; 幽灵返回值先声明; 同时给出行映射 (每行属于哪个client的哪条语句).
- 类型不变式的类型 (`#[verifier::type_invariant]`: guard, `FrameRef`, `Rcu`..) 的exec或tracked值, 在client看得见不变式之处 (类型自己的模块之内) 的绑定处加`proof { use_type_invariant(..); }`; 兄弟模块中看不见 (见下). 每条路径末尾一个`assert(false)` (空洞性断言), 模块中一个必定失败的sanity client.
- **client放在被测模块的兄弟模块中** (`mm::frame::segment`的client在`mm::frame::cs_clients`, 文件`mm/frame/cs_clients.rs`, 在父模块的文件中声明; 顶层模块的兄弟在crate根). Verus让closed的spec函数体和私有字段对定义它的模块**及其子模块**可见. 前身把client放在被测模块之内 (子模块), client于是比别的模块中真实的调用者看得多: 结果只由closed函数描述的API (`Segment::split`的`split_spec`, `From<Frame>`) 在那里量不到, 这一类缺陷系统地漏掉 (enumeration.md 17.3: 加了`assume(!P)`之后完全量不到; 20: 同一批client放到兄弟模块, segment有25个由通过变为失败, 正是已确认的缺陷, spin多出`wf`的候选). 兄弟模块看得见表中的一切 (都至少`pub(super)`), 导入是表的导入, `use super::NAME::*;` (模块的项), 和模块顶层的`use` (照抄, 它们的`super`对兄弟也一样; `use self::`改经模块; `#[cfg]`之后的不取).
  - 代价1: 兄弟仍看得见**父模块**的closed体, 只是往上一层, 不是完全没有. 要完全模拟别的模块中的调用者, client要放在另一棵子树中, 那时`pub(super)`的API就看不见了; 一层是可调用性与可见性之间的折中.
  - 代价2: 类型不变式 (`use_type_invariant`) 只在类型自己的模块之内可用 (has-type-invariant?的规则), 兄弟中不再加. 这与别的模块中的调用者一致: 前身认为"不变式给出的事实不算规格的缺口", 那只对看得见不变式的调用者成立; 公开的规格若要调用者知道不变式推出的事实, 要由ensures或公开的谓词给出 (spin的`wf`, enumeration.md 20).
  - 代价3: 结果与前身的不能逐个对照; 改了放法的一次运行要整体重新判定.
  - 父模块的文件找不到时 (经`#[path]`挂载的模块) 退回子模块, target记`(placement child)`, 结果中可见.
  - 导入的细节 (都是第一次从零重做时由探针的编译错误发现的): 不再`use super::*` (那是父模块的项, 与模块的同名: vm_space的`Cursor`与page_table的, E0659); 模块声明的非私有类型显式导入 (`use super::vm_space::{Cursor, ..}`): 模块之内它自己的定义胜过一切glob, 兄弟中模块的项也是glob, 与模块自己的glob导入相撞, 显式导入胜过glob; 模块自己已导入的名字, 表不再导入 (E0252); 经私有子模块的`use`不取.
  - 模块的自由函数写绝对路径 (`crate::mm::frame::meta::get_slot`), 不写`super::f`: 后者只在模块之内对. 绝对路径从兄弟和从能到达它的别的模块 (协议) 都对.
  - 一个模块的运行表并入别的模块的表时 (协议调用它们的API) 只取条目, 不取导入 (`(base FILE entries)`): 导入是相对于那个模块的位置的, 并入之后相撞或解析不了; 那个模块的项由`use crate::<它>::*`导入. 那个模块是父模块的私有子模块时 (`mm::page_table::cursor`, `node::child`, `dma::dma_stream`: 父模块经`pub use`重新导出它们的项), 这一行在兄弟中不能写 (E0603), 整个模块编译不过; 别的模块中真实的调用者也写不出它, 只能经重新导出. 所以rustc对表自己的某行`use`报E0603时, 下面的导入轮次中把这一行去掉 (结果中记`(dropped-imports ..)`), 缺的名字由重新导出或下一轮的建议补上; 哪条路径可写不由我们解释Rust的可见性来判断 (2026-11-16, 第一次全部模块的运行中mm.dma, mm.page_table, mm.page_table.node因此没有结果).
- 运行: 只验证client模块. 解析每个错误, 按行映射归到语句; 编译错误归不到时按错误中第一个落在client中的位置归因.
- 导入: client还会用到别的模块的类型 (协议调用别的模块的API, 签名中提到本模块没有导入的trait). 在client的位置能看见什么只有rustc知道 (私有模块的路径不能用, 别的模块私有的`use`带不过来), 所以不由VIR的路径拼导入: 一个模块跑完后, 编译错误中只有一个候选的导入建议 (规则同表的机械修补) 加进本次运行的表, 整个模块重跑, 通过的不减少才采用. 要重复几轮 (至多3轮): rustc分阶段报错, 先是找不到的名字 (`SpinGuardian`), 名字都解析了才报方法 (`deref`所属的trait不在作用域中), 所以下一阶段的建议要等一轮之后才出现 (只做一轮时, `rwarc`的4个协议client停在`deref`上). 整模块重跑, 因为一行显式的导入会遮蔽glob导入的同名项, 可能改变别的client. 原型另试过一种做法: 读别的模块源码顶层的`use`, 取签名中用到的名字的那些 (连同glob和`#[cfg]`), 改成绝对路径. 它能用, 但要自己解析Rust的路径 (`super::`, `self::`, `mod.rs`中指子模块的相对路径, 被`cfg`关掉的), 全取又会碰上别处的私有导入 (E0603) 和同名的冲突 (E0252); 由rustc的建议导入不必知道这些, 所以不采用.
- 经过client模块本身的导入建议 (`use crate::mm::page_table::cs_clients::array_ptr::ArrayPtr;`: client模块`use`了一个模块时, rustc会经它建议) 只在那个模块中成立, 而表也从别的模块用 (一次因此整个cursor模块编译不过): 改写为经client自己的那条导入 (`use vstd_extra::array_ptr::ArrayPtr;`), 没有那条导入就不采用.
- 续跑: 一个模块的结果只在client, 表的导入, 对表展开后的client (client.rkt的展开: 断言和提升的requires), 渲染和运行的代码 (render.rkt, run.rkt, module-run.rkt, repair.rkt的哈希), 检出的状态都没变时才沿用; 导入的轮次和崩溃后的对半拆开在module-run.rkt, 选哪些导入在repair.rkt, 它们都改变一个模块的结果 (到2026-11-16它们在evaluate.rkt中而不在键里, 改了导入的规则之后要手工删去`key.sha`); evaluate.rkt的其余部分 (配置, 汇总) 不在键里, 改了它不重跑; 只看client和检出时, 改了修补或渲染之后续跑会悄悄沿用旧的结果; 不看展开时, 表的条目或client.rkt改了也一样 (2026-11-11).
- 编译错误使整个模块不被验证: 去掉有编译错误的client重跑, 至多几轮.
- Verus本身崩溃 (求解器panic, 内存耗尽) 不是任何client的错: 不丢弃client, 把这批client对半拆开重跑, 递归到一个下限, 再合并结果.
- 运行结束时 (包括出错时) 删去client模块, 还原模块声明, 恢复被验证改写的`Cargo.lock`.
- client的共享引用参数写成`&'a T` (client有`'a`时): API可能要它活得一样长 (`cursor(&'a self, guard: &'a G, ..)`, 而VIR和表丢了引用的生命周期, 写成`&G`时E0621), client的函数体总可以借得更短; client从不被调用, 收紧它的签名不损失什么.
- Verus以`--expand-errors`运行: 每个函数第一个失败的断言, 若是不透明的谓词 (`clone_requires`, `relates_owner`), 被展开到失败的合取项, 出现在该函数的错误之后的一个note中. 解析时把note归给同一client的这串错误中的第一个, 并要求note的表达式就是它的文本 (否则丢弃), 记为`(expanded (FILE:LINE 失败的文本) ..)`. 代价约10%的验证时间.
- Verus把经`#[path]`挂载的文件 (`specs`) 写成`ostd/src/../specs/..`: 路径中的`dir/..`先去掉, 否则错误对不上client模块, 所有client都像是通过了.

### 3.9 判定的辅助, 不是判定 (原则2)

- "可能panic"子句 (`P ==> may_panic()`, `may_panic`不解释) 只能由证明非P满足. 不调用到panic是**调用者的选择** (真实的调用者先查对齐, 计数), 不是前面的调用欠它的事实: 所以client在每个调用 (和每个`assert-requires`的这条子句) 之前`assume(!P)` (`check/client.rkt`的`with-no-panic`, 嵌套的`A ==> (B ==> may_panic())`给`A && B`), 而不是断言非P. 非P在那里不可能时路径空洞, 由路径末尾的空洞断言报出. 以前 (到2026-11-15) 断言它, 每个走到`read_once`, `fill`, `split`的client都在这里失败, 失败之后的事实都量不到 (enumeration.md 17).
- 仍只败在"可能panic"子句的client单独计数 (例如可信代码中的panic条件, 和规则之外手写的client). 三种形式都算: client自己断言的requires; Verus报为被调用者前条件的 (`callee`的源码行); 不透明子句展开后只有`may_panic()`失败的.
- 不透明子句的失败按展开后失败的合取项分组 (至多取4项), 而不是按子句的文本.
- 按失败的子句分组, 而不是按client. requires子句按身份 (被调用者, 第几条; 组名`requires of API /N`, `(text ..)`是一个例子), 不按文本: 文本随client的变量名而变 (goal的`self_g`, protocol的`x0`), 同一条子句分成几组 (2026-11-13, r23按文本1475组, 按身份807组). goal的出错之后的client按出错的调用归为一组 (`after an error of H`, `(clauses ..)`列出G的子句). 一组中有多少client的这条子句把新参数和产生的值绑在一起记为`(tied N)`, 全部如此的标`(noise tied)` (goal-shapes.rkt的`tied-clauses`). claim和关系仍按文本 (变量名遮去).
- 用调用知识给失败的子句加标签; 只用关于失败的那个API的条目 (用关于client中任何API的条目会标注几乎一切, 掩盖候选).
- **连锁失败按路径标出, 不删去.** 失败的断言之后Verus假定它成立, 所以同一路径上后面的失败可能只是前面的后果 (一个函数丢了事实, 之后每个调用都失败). 语句的id (render.rkt: `s2.4.e1/1`是语句2的then分支中语句4的else分支中的第1句的第1条子句) 给出路径上的先后: 前面的语句, 或同一语句前面的子句. 每组记`(first N)`: 有多少个client中这条子句是路径上第一个计数的失败; 其余的记`(after (前面的子句 次数) ..)`, 取路径上最早的那个. `(first 0)`的组 (2026-11-11的r12中965组里有197组, 1124个client) 要等它所在的组修好再看. 只是先后, 不是因果: 后面的失败也可能是独立的缺陷, 所以不删, 排在后面.
- **已知问题也作为标签** (`groups RUN KNOWLEDGE ISSUES`). 证人的`(fails ..)`说的是证人在哪里失败, 不是问题在别处的样子 (`[.]inv[(][)]`), 所以只在调用了问题的主体 (证人的第一个调用, 规格有缺口的那个生产者) 的client中, 匹配的失败才标为`(issue ID)`. r12中217组有这样的标签.
- 两次运行之间按client名字对比状态, 找出由通过变为失败的.
- **包装函数丢了什么** (`racket cli.rkt drops`, `lib/pipeline/drops.rkt`; representation.md 6.6). 本轮判定出的缺陷最多的一类是: 函数F调用G, G的ensures给出的事实F自己证得出, 却不在F的ensures中 (dma的`reader()`丢了`reader_inner`的`read_view_initialized()`). 机械地找, 分三步, 后两步都由Verus决定:
  1. 候选 (静态): F的函数体 (VIR) 调用的每个G, 把G的ensures子句 (源码的树) 搬到F中: G的参数换成F的参数 (只当实参就是F的某个参数时), G的结果换成F的结果 (类型相同时; F返回G的结果包在`Ok`/`Some`中时写成`r is Ok ==> (P[r.unwrap()])`), G的ghost结果换成F的同类型的ghost结果; G的不可变参数而实参是F的`&mut`参数时, 换成`final(p)` (F返回时的值; F在调用之后又改了它的, 下一步去掉). 还提到G的别的东西 (局部值, 没对上的参数) 的子句不要, 只有常量的不要 (`PagingConsts`的引理那样的事实不是包装函数该给的), 带量词的不要 (树中还没有trigger), F的ensures中已有的不要. 搬法是粗的 (不看数据流): 错的候选由下一步去掉.
  2. F证得出吗: 在vostd的副本中, 把一个模块的候选加进各自F的ensures, 验证整个crate; Verus对每条没证出的后条件分别报错, 去掉它们 (以及编译不过的) 再验证, 直到没有错误. 留下的是F的函数体证得出的.
  3. 调用者得得到吗: 对留下的每条, 生成claim client (调用F, 断言它), 在原版的检出中运行; 失败的就是"F证得出, 却不告诉调用者"的事实. F的ghost结果是`Option`而F返回`Result`时, claim再加上`ret is Ok ==>`: F的ensures把事实写在`r is Ok`之下, 没有东西把`Some`和`Ok`联系起来, 只有`is Some`的claim会因此失败 (DmaStream的`reader`的`inv()`那样), 而加了它仍蕴含于第2步证出的.
  第2步改写的是副本 (每轮先还原, 最后还原, 证出的存为`survivors.patch`), 不用环境的检出: 那是运行client的地方, 而第3步要在没有这些ensures的原版上运行. 每一步的产物都在输出目录中, 中断后续跑.
  一层一层地做 (`--base PATCH`): 修好F之后, 调用F的上一层又可能丢掉F新给的事实 (page-table的cursor给了`barrier_va`不变之后, vm_space的cursor是否传下去). 这时分析的是打了补丁的vostd: 环境的检出 (`CS_ENV`指定的打了补丁的副本) 是第1步读源码, 第3步运行的地方, COPY每轮还原之后再打上同一补丁. VIR仍是原提交的: 补丁只改规格, 不改函数体, 第1步所跟的调用不变.
  产出的是事实 (证得出, 没导出), 不是判定: 调用者需不需要, 由人判定 (原则2).
- **手写的修改的确认 (`fixes`).** `provable`/`confirm`只能确认"给责任者的ensures加一条它的形参写得出的子句"; 别的修改 (没有ensures的函数, `dual_spec`改为`dual_spec, open`, 改一个open的spec函数, 下层和上层一起改) 以前由人逐步手工确认 (evaluation.md 第8节, 2026-11-16的N27-N29). `fixes`把那几步机械化: 修改是数据, `(fix ID (groups (M KEY) ..) (why ..) (replace FILE OLD NEW) ..)`, 每处是对检出中一个文件的**精确替换** (OLD在文件中恰好出现一次, 否则这个修改是`bad-edit`, 不猜; OLD和NEW取所改文件的行尾: 在Windows的检出 (`core.autocrlf`, CRLF) 上写的修改, 用在WSL中LF的副本上意思相同). 然后: 全部打上, 验证 (依赖的crate如bitflags在同一输出中), 错误按位置归: 落在某个修改的新文本中的归那个修改; 别处的映射回原来的行号, 由VIR找到所在的函数, 归给改了它调用的函数或同一模块的函数的修改 (`breaks-proof`, 理由同`confirm`); 去掉归到的修改再验证, 直到没有错误, 归不到的停下. `breaks-proof`的归属只到模块, 一次会去掉同一模块的几个修改 (r1: 一处segment的证明失败, segment.rs上的7个修改一起被去掉, 其中有自检时单独成立的`into_raw`), 所以因`breaks-proof`被去掉的, 逐个在留下的修改之上再试一次 (`retry`), 验证通过的留下. 留下的按槽单独验证 (`alone`; 槽的目录按其中的修改命名, 修改的集合变了不会沿用旧的结果). 再全部打上, 以副本为检出重跑目标组所在的模块, 分组, 与运行逐个client比较: 每个修改的每个目标组前后的client数, 新出现的组, 由通过变为失败的client. `confirmed`: 单独成立, 目标组都降到0; 只降到0一部分的, 按组读 (`alone`且这一组`AFTER`为0, 这一组由这个修改确认); 没有重跑的模块 (没有留下的修改指向它) 的组记为`not-run`, 不是0. 一个修改可以建立在另一个修改之上 (下层的修改给了事实, 上层的修改往上传, 如`CursorMut::query`转述`Cursor::query`新给的ensures): 分槽时它与它所依靠的修改是相关的, 不在同一槽中, 于是单独验证时它证不出 (`unproved`), 而这不是它的错. 所以单独证不出 (`unproved`) 的修改, 与它所改的函数 (传递地) 调用的函数上**单独成立**的修改一起再验证一次 (`with`); 通过的记为`(with ID ..)`: 它所依靠的都已单独成立, 合起来是证明的组合, 与`alone`同样算数 (r1第三次: `cursor2-1`, `cursor2-2`, `cursor-14`, `list2-1`都是这样). 只看调用, 不看同一模块: 同一模块是`breaks-proof`的理由 (求解器的扰动), 不是事实的来源. 重跑中由通过变为失败的若是rlimit, 是修改的代价 (更多的事实使长的client证明变慢), 不判定. 一个目标组的`AFTER`数的是**原来这组的client**中, 修改之后仍在这组的, 加上改为rlimit超时的: 超时的client只报一个超时, 不进任何组, 它在这一子句上的结果是未知, 不是通过. 以前`AFTER`数的是重跑中这组的client, 原来这组的client若改为超时, 组就降到0而算作清除 (r1: R17多确认的`unmap /2`, 第三次时它的3个协议client都超时了, 第七次别的修改使它们不再超时, 又在这一子句上失败; 2026-11-17). **冻结的基线 (`--base`).** 一轮中`fixes`会跑几次: 先确认一批, 再为没有确认的写新的. 以前每次都把已确认的修改和新的一起重新分槽, 单独验证 (r1第七次: 108个修改中90个早已确认, 28次验证), 新写的修改还可以替换已确认的修改, 替换之后不成立就连已有的确认一起丢掉, 只好退回再跑 (r1第三, 五, 七次都是这样). 所以已确认的修改作为**基线** (`--base FILE`, 修改的数据): 每次验证都先打上, 不分槽, 不归错, 也不能被替换 (新修改用了基线中的ID, 停下; 与基线的编辑重叠, 是`bad-edit`). 先只打基线验证一次, 不通过就停下 (基线是证过的, 不通过说明副本或基线变了). 新修改的错误照旧归: 落在基线的新文本中的, 按那一行所在的函数归给改了它调用的函数或同一模块的新修改; 归不到新修改的停下. 新修改在基线之上分槽, `alone`即"在基线之上单独成立"; 基线已证, 合起来仍是证明的组合. client只重跑新修改的目标组所在的模块; 以只打基线的那次重跑 (`--base-run DIR`, 通常是上一次的`after/`) 为前, 这样组降到0是新修改的功劳, 不是基线的. 下一次的基线由`fixes-base FACTS FIXES-FILE [上一次的基线]`取出: 留下, 且单独或`with`成立的修改, 接在上一次的基线之后. **并行 (`--copies`).** 单槽 (`alone`) 和`with`的各次验证互不依赖 (每次从原文重新打上自己的修改), 可以在几个副本中同时做; 一起验证的各轮和`retry`依赖前一次的结果, 按次序在COPY中做. 每个副本有自己的cargo目标目录 (目标目录加`-K`), 不能共用 (cargo的锁, 增量的产物). 副本与COPY同一提交, 干净, 不是环境的检出. 一次验证整个ostd约50秒, 占几GB内存; 15 GB的机器上用2个额外的副本. 结果与不并行时相同 (每次验证的输入相同, 结果按槽和修改记下, 与次序无关). **修改的标记.** 每个修改的事实带两项, 供判断它能不能不经人看就记为已确认的缺陷 (workflow F5): `(rests-on ..)`, 它所改的函数依靠的可信代码 (函数体中的`assume`/`admit`, 调用的`external_body`函数, 同`confirm`的`rests-on`); `(attributes ..)`, 新文本中的`#[verifier::..]`属性和`assume`/`admit` (不是规格的改动: r1的misc-11加了`loop_isolation(false)`). `rests-on`中有`assume`/`admit`的, `attributes`不空的, 由人决定; 只调用`external_body`的不算 (几乎所有修改都如此), 列在记录中. 修改是否经open的spec函数加强了`external_body`函数的契约 (r1的R50), 工具还查不出, 由写修改的人和判定的人看. 与`provable`一样, 证得出不等于调用者需要: 那是判定 (原则2).
- **`confirm`中不落在候选行上的错误.** 一个槽的子句单独加上时, 别的函数中**原有的**证明可能失败: r1的第3槽中`VmWriter::fill`的循环证明 (io.rs:449, 一条模运算的`assert .. by`) 失败了, 而`provable`把全部子句一起加时它通过了. `fill`不调用槽中的任何函数; 与它有关的是**模块**: 槽中的`write_val`, `write_once`, `read`也在`mm::io`中, 而Verus在一个求解器中依次检查一个模块的函数, 一个查询变了, 别的查询也会动, 脆弱的证明就可能失败. 所以这样的错误归给槽中能够影响那个函数的查询的子句: 它调用的函数的 (它的证明假定它们的ensures), 或同一模块的函数的; 记为`breaks-proof`: 子句成立, 但单独加上会使原有的 (脆弱的) 证明失败, 是修改的代价, 不算`confirmed`. 归不到任何子句的错误仍停下. (2026-11-16. 第一次的规则只看被调用者, 理由写成"`fill`调用`write_val`", 是错的: 对照VIR, `fill`不调用它们, 规则也就归不到; 改为加上同一模块.)
- **`provable`的一次分析是一个固定的实验.** 它试哪些组 (`--unlabelled`: `groups`中没有标签的, 即一轮的新组) 在第一次运行时记下 (`provable/selection.rktd`), 续跑试同样的组; 候选子句按集合与`cand.rktd`比较, 序号沿用`cand.rktd`的 (`rounds.rktd`按它记谁被去掉). 以前按当前的标签重新选, 按组的次序排候选: 写下判定 (加了标签) 之后组少了, 而`groups`又把`provable`证出的组排在前面, 即使什么都没改, 第二次运行也因候选的次序变了而拒绝续跑 (2026-11-16). 换模式, 记下的组没有了, 或候选子句变了 (运行或表变了), 才拒绝, 那时是另一个实验.

### 3.10 ensures的覆盖 (原则2, 5)

client的失败指出requires的缺口; 反过来的问题是**哪些ensures子句没有任何client检验**: 一条子句没有client的证明需要它, 它写错或缺了, 评估都发现不了 (测试一侧的pseudo-tested, 形式验证一侧的覆盖; 前身survey的I, J卡片). `coverage RUN-DIR`回答它 (`lib/pipeline/coverage.rkt`):

- 每个模块一次Verus运行, 加`--log smt`, 每个client一个SMT文件 (每个client有`spinoff_prover`). Verus把被调用者F的ensures编成一条公理 `ens%F(..) = (and 自己加的合取项.. c_1 .. c_n)`, 每条子句一个合取项 (字面上为`true`的子句被丢掉: 合取项数与表的子句数对不上时报`count-mismatch`, 不用F).
- 在文本上 (日志中有`#x..`之类的字面量, 经s表达式读写会变) 给运行的表中每个API的每个合取项加守卫`(=> g c_j)`, client的查询中每个`(check-sat)`换成`(check-sat-assuming (g ..))`. 最后一次check-sat是"其余断言都证出"的那次: 之后问unsat core, 再对每个守卫问一次"它为假, 其余为真". 不是unsat: 这个client需要这条子句. 用检出中Verus自带的z3重放, 一半的核并行.
- 这正是前身X9 (删去一条子句, 重跑, 看谁新失败) 的问题, 代价是一次运行加几十秒z3, 而X9每个模块要几十轮 (每条子句一轮). 在segment上两者给出同样的9条子句, 差别都是求解器的不稳定 (enumeration.md 18.2).
- **不是回答的不算** (enumeration.md 19): 最后一次不是unsat的client (失败了, 或重放超限) 什么也不需要; 守卫为假时`unknown`且原因是资源上限的, 记为`limit`. 只被`limit`涉及的子句是`unknown`, 不是`unchecked`.
- 结果`RUN-DIR/coverage/<m>.rktd`: 每个client需要哪些子句, 模块自己的每个API的每条子句是`checked` (由谁), `unknown`或`unchecked`. 续跑: 模块的结果的键没变就不重跑.
- 局限: (1) core只来自最后一次查询, client中失败的断言之后被假定的那段照样算 (与X9相同); (2) 守卫改变了z3的搜索, 个别查询与原查询不同; (3) 一条没人检验的子句可能是由其余子句推得出的 (前身的E2: 观察上多余); 本版不再问, `unchecked`的子句要读规格判定是缺client还是多余; (4) 只看ensures, 不看requires是否太强.

### 3.11 已知问题的回归 (原则2, 7, 9)

确认过的问题是基线: 换了vostd提交, 改了工具或数据之后, 第一个问题是"已知的每个问题还在吗, 还检出吗". 这必须是一条命令, 不能靠人记得去做 (一轮评估曾因此重新发现了一部分已知问题, 漏掉了其余的). 所以已知问题也是数据 (`data/issues/*.rktd`, 格式在`lib/model/issues.rkt`), 与判定分开 (原则2): 数据只说"这个问题由这些client显示, 应当在这里失败", 问题是否成立仍是人的判定.

- **证人是client本身.** 每个问题有一个或几个证人: 显示它的client (完整的client形式, 从某次运行中取出或手写) 和它应当失败之处. 不存生成的名字或组的键: 重新生成后名字和组随生成器而变, 而存下的client不变. 期望写成失败之处而不只是"失败", 因为同一client常常还因别的问题失败.
- **期望按子句的身份**, 与写法无关: `(fails (requires API N))` (证人中API的第N条requires, 由语句的id的`/N`和行尾的`// requires of API`认出), `(fails (claim))` (claim的断言). 表的子句次序变了 (vostd改了requires) 时要改N. 前身还允许对渲染出的文本写正则, 渲染一改就对不上, 问题被误报为gone (time-sinks C16); 本版读入这样的期望但不用, 只有文本期望的证人不算, 问题报为`no-witness`并说明要改写 (前身数据中116个证人有11个是这样).
- **运行与评估相同.** `regress`只跑证人, 表按配置的`auto`建 (证人调用的别的模块的表也并入), 运行目录, 续跑的键, 导入的修补都与评估一样 (`compare`照样可用). 检出由环境决定: 对原版跑一次, 用`CS_ENV`对打了补丁的检出再跑一次.
- **状态是机械的.** 每个证人: `shows` (失败, 有错误匹配期望), `passes` (通过, 没有空洞), `other` (只在别处失败, 没有空洞), `vacuous` (有空洞的路径: 那条子句可能只因路径不可行而成立), `broken` (编译错误, 不良构: API的签名变了), `not-run`, `not-concluded` (sanity不是ok). 每个问题在原版上: `present` (有证人显示它), `gone` (每个证人中那条子句都不再失败, 即`passes`或`other`: 上游修了或规格变了, 对照diff判定), `undetected` (都不是: 证人要重新取), `no-witness` (没有能运行的证人, 数据写明为什么, 例如要往返的声明或某个claim); 在补丁上: `fixed` (每个证人`passes`或`other`), `not-fixed` (有证人仍`shows`), 或`undetected`. 判据是那条子句, 不是整个client通过: 证人常常还撞着别的问题或噪音 (计数饱和), 修一个问题不会使它们通过; 失败的断言之后Verus只假定它成立, 后面的子句照样检查, 所以别处的失败不影响这条子句的判断, 空洞的路径才影响.
- **取证人.** `witness RUN CLIENT ..`从一次运行中取出client, 以它第一个不是panic的错误的身份 (`(requires API N)`或`(claim)`) 作为默认的期望, 打印成证人; 认不出身份时写`(EXPECTED)`, 它不是合法的期望, 读入时报错, 要人写. 人再确认那就是问题的那条子句.
- 证人的client也受表的版本检查: 表换了提交, 证人随之对新的表检查良构, 签名变了的报为`broken`, 而不是悄悄地不跑.

### 3.12 可信代码 (原则2, 5, 7, 9)

合成client只检查规格"够不够用"; 被Verus信任而不验证的地方 (`assume`, `admit`, `external_body`, `external`, 公理, `assume_specification`) 是否比实际行为强, 是另一件事. 列举是机械的, 判定是人或LLM的, 演示把一部分判定变成可以重跑的事实. 三者分开 (原则2), 判定是数据 (原则7), 每层有自己的核对 (原则9).

- **列举** (`lib/vostd/trusted.rkt`). 只读源码 (git中某个提交的文件, 不看检出中未提交的改动), 不靠VIR: VIR中`external`的东西不存在, `assume`是表达式中的一个结点, 不带它所在的语法位置. 一个小的词法分析 (注释, 字符串, 字符常量, 原始字符串) 加上括号的配对就够: 每个条目得到它在文件中的路径 (`<Frame as NonNullPtr>::into_raw`, `TlbFlusher::issue_tlb_flush`, `[SmallVec::<A>::index]`). 规格中的块 (`ensures match x { .. }`) 由右括号之后跟着什么 (`,`, `else`, 运算符, 下一个子句) 认出, 不是函数体.
- **身份不用行号.** 一处可信代码的身份是 (种类, 文件, 条目的路径, 细节); `assume`的细节是它的命题, 同一条目中相同的再加`#2`. 行号只为读. 这样判定跟得上代码的移动, 而改了的命题是新的一处.
- **指纹.** 判定针对的是它看到的文本: 属性和条目是整个条目 (属性, 签名, 规格, 函数体: `external_body`的函数体就是"实际行为"), `assume`和`admit`是它所在的整个函数 (前面的证明变了, 命题是否成立也可能变). 注释, 字符串的内容, 空白不算. 指纹变了, 判定要重新做; 没变, 判定在新提交上照样成立. trait方法的规格写在trait声明中, 不在impl方法的指纹里 (查不出; 声明也是可信代码的那部分由声明自己的条目负责).
- **判定是数据** (`data/audit/verdicts/<区域>.rktd`, 格式在`lib/model/audit.rkt`): 每条判定是几处 (一行审计常判一组: 同一类型的Send和Sync), 带判定, 理由, 原报告的编号, 对应的演示. 区域有范围 (目录或文件), 范围内没有判定的是"未判定". 详细的推理留在审计报告 (`data/audit/<区域>.md`) 中, 数据只引编号.
- **核对** (`audit`): 判定对着检出的HEAD, 报告变了的 (指纹不同), 没了的, 改了名的 (没了的那处的指纹原样出现在一个没有判定的新名字下), 未判定的, 同一处判定不一致的 (两份报告对同一处判得不同), 以及演示在某次运行中的状态. 重新判定之后`--accept`写入新的指纹和提交. 不再可信的 (函数体被验证了, 规格移到了vstd) 不删, 记`(removed 提交 理由)`; 关于几处的用法的判定 (例如一个公理可以在任何证明中调用, 或一种权限可以伪造) 记`(aspect usage)`, 不与各处自己的判定比较.
- **演示** (`demos`): 把too-strong的结论写成只用公开条目的Verus代码 (证明`false`, 或明显错误/不安全的事实), 不用`assume`/`admit`/`external_body`; 每个模块一个必定失败的`demo_sanity`, 它必须是唯一的错误, 否则 (编译不过, 别的错误) 什么也不能断定. 运行的目录与评估的相同 (清单, `results/<演示>/results.rktd`中每个演示函数一个`client`, 续跑的键), 所以`compare`逐个比较两次运行. 演示是手写的Rust, 不是生成的client: 它要实现trait, 写辅助的证明, 不在client的表示之内, 所以不作为族注册, 只共用运行目录和结果的格式.

## 4. 必须注意的事项

### 4.1 Verus和验证的语义

- **失败的断言之后Verus假定它成立.** 后面的断言可能借它的光而"通过", 后面的路径可能被报为空洞. 修好前面的失败再看后面; 空洞性判定只在没有更早的失败的路径上可靠.
- **空洞有两种:** 假定矛盾 (client的requires, 表的requires, 之前失败的断言), 这时路径上的结论无效; 或者路径经过规格排除了的分支 (Err之后再调用得到Some), 这时它是一个事实. else分支的组合尤其常见后者.
- **空洞性断言只在路径末尾.** 一个分支的末尾另加断言不行: 失败的`assert(false)`之后一切都空洞.
- **`(sanity ok)`才可信.** 没有`verification results`一行, 或sanity不恰好失败一次, 这个模块没有真的被验证.
- **`cargo dv verify`也一样**: 源码与上一次在同一目标目录中验证过的相同时, 它只打印`Verified ostd .. in 0.59s`, 没有`verification results`一行. 它按内容判断, 不按修改时间: `drops`/`fixes`的每次验证之前在`ostd/src/lib.rs`末尾加一行带时间的注释 (不移动任何行), 验证完写回原文, 让它真的重新验证 (r1: 第七次的108个修改原样再跑, 第一轮就因为没有结果而停下; 2026-11-17).
- **`cargo dv focus`在源码没有变化时直接给出上一次的结果**, 即使`--verify-only-module`不同; 要改动一个文件才会重新验证. 先看输出中"verifying module"是不是要验证的那个.
- **Verus会崩溃** (求解器panic, 内存耗尽). 崩溃的输出中没有完整的结果, 不能当作编译错误处理, 也不能保留其中的部分结果; 对半拆开重跑只是后备. 以前大模块的崩溃来自下一条所说的长z3会话, 不是client的个数本身.
- **Verus给一个模块一个z3会话.** client都在一个模块中, 不加属性时整个模块在一个z3中**串行**验证 (32核的机器上只有一个z3在跑), 而且这个z3一直累积: cursor模块155个一批在约18分钟后崩溃 ("expected rlimit-count in smt statistics"), 对半拆了7次, 整个模块用了3.5小时. 所以每个client带`#[verifier::spinoff_prover]` (render.rkt): 各自一个新的z3, 按线程并行. 同样的619个client一批11分钟, 不崩溃, 每个client的状态不变 (只有rlimit与被它挡住的`may_panic`断言不同); segment从354秒到66秒. 每个client的结果也不再取决于同批的别的client (rlimit的结果原来取决于共享的z3的状态).
- 并行之后内存是限制: 每个z3约200–350 MB, rust_verify约1.5 GB (7.7 GB, 31个z3时用了6 GB). 线程数由`verus-threads`给出, 不给时按`/proc/meminfo`估计 (run.rkt的`default-threads`).
- 每次运行在结果的`(run ..)`中记下每次尝试的秒数 (`seconds`). 以前只能从文件的修改时间重建, 而且一次"vm_space生成client用了三小时"其实是机器睡眠了 (Windows的Kernel-Power事件42/107), 生成只要32秒.
- `rlimit`超时不判定, 单独列出.
- **一个错误的块只到下一条独立的提示为止.** 解析Verus的输出时, 一个`error`之后到下一个`error`/`warning`之前的行, 不全是这个错误的: Verus自己的提示 (`note: recommendation not met`, 展开, 进度, 以及`note: automatically chose triggers for this expression`和随后的`Verus printed one or more automatically chosen quantifier triggers`) 是另外的诊断, 它们的`-->`位置不是这个错误的位置. 以前触发器的提示没有截掉, 它指向的位置被当作错误的位置之一: r1的`fixes`中, frame6-1的引理中的一处失败 (linked_list_owners.rs:595) 之后Verus恰好为frame-8新加的ensures (segment.rs:641) 打印了触发器的提示, frame-8于是被一起归为`other`而去掉, 失去了已确认的R54 (第一次第3轮, 第二次也是这样被去掉的; 2026-11-17).
- **Verus的版本跟着vostd走.** vostd不固定Verus的版本, 跟着`asterinas/verus`的`main`; 新的vostd提交可能要新的Verus (`4ec330ec2`要`vstd::std_specs::ptr`). 原版`ostd`必须先0 errors, 才往下走.
- **Verus在Windows上的误报.** `84ae63ed`的`proof_with!`检查 (#3372) 比较标识符的span时连span的parent一起比, 在Windows上对每个`#[verus_spec(with ..)]`的调用误报"resolves to `f`, not to `f`" (Linux的CI通过). 在本地改为只比较起止位置可以绕过. 确认的办法是在最小的例子上复现 (位置相同而parent不同); 先怀疑过的CRLF和过期的构建目录都不是原因. 对Verus的修改要在记录中写明. 新的Verus是否还有这个问题, 用原版`ostd`是否0 errors判断.

### 4.2 Rust和VIR

- VIR抹去了: 引用的生命周期, 自动取引用和解引用, 有界整数的扩展, trait实现中方法的requires, `Tracked`包装的位置. 每补一项都要重新抽取全部表并逐条看差异: 第一次补`Tracked`时对所有读取都加, 使75个原来通过的client编译不过.
- 生命周期的近似 (一个`'a`; `&'a T<'a>`) 在可变引用上不成立 (不变性).
- **由VIR写回调用的形式** (`specs::*`第一次被真的探针之后发现的). 2026-11-13起子句照源码写, 与VIR按结点的跨度对齐: 写法取源码, 被调用的项, 常量, 绑定变量的类型, Tracked的包装取跨度相同的VIR结点 (`source-spec.rkt`, representation.md 10). mm和sync的2118条requires中1943条这样得来; 下面的规则对子句只用于其余175条 (136条是没有源码的条目的, 13条在vstd的trait中, 26条是宏或带语句的块), 此外用于条目本身的调用写法 (`call`) 和对齐时取的VIR名字的限定部分:
  - 一个调用是否经trait (`<T as Tr>::f`) 按VIR中的trait列表判定, 不按路径倒数第二段是否大写: `vstd::set::Set::empty`是结构体的函数. 数据类型的函数, 前几个类型实参属于类型 (个数是它的类型参数个数), 写成`Set::<T>::empty()`, 不是`Set::empty::<T>()` (E0107).
  - 元组结构体唯一的变体与结构体同名: 构造写`PageTableOwner(x)`, 不写`PageTableOwner::PageTableOwner(x)` (E0599).
  - `arrow_N`/`arrow_Name`访问函数 (含vstd的`OptionAdditionalFns::arrow_0`, 即Option的`x->0`) 写回`x->0`; 经trait的路径调用时它要`&x` (E0308).
  - 源码中显式的`&p` (p不是引用) 在VIR中是借用p的临时位置: 保留为`&p`, 否则被调用者得到值 (`untracked_range_slots_in_regions(&pa_range, ..)`).
  - trait方法的trait有类型实参时 (`TreeNodeValue<L>`, `Repr<MetaSlotStorage>`, `From<UniqueFrame<M>>`), 调用写`<Self as Trait<..>>::f`, 实参中的类型参数也用`{X}`待实例化; 作为方法调用, trait的实参推断不出 (E0284, E0107). 方法自己的类型参数中没有参数提到的 (`fill_panic_condition::<T>`, E0282) 写出; 被调用者的参数类型是它的类型参数时取调用的实例 (`Repr::wf(r: R, ..)`中R的实例决定要不要`*slot`).
  - const泛型 (`const L: usize`) 是约束`(const usize)`, 渲染为`const L: usize`.
  - 元组的字段是`Tracked<T>`而值是T时 (proof函数解开的tracked参数) 包回`Tracked(..)`.
  - spec函数的结果的类型参数没有参数决定时, 绑定写出类型 (`let ghost r: PageTablePageMeta<C> = ..`, E0283).
  - 经trait的路径写的vstd spec方法 (`VecAdditionalSpecFns::spec_index(&frames, i)`) 没有自动取引用: 接收者在VIR中是借用而所读的位置不是引用时写`&`. 方法调用改经trait只在trait的实参有self类型没有的类型参数时, 接收者按被调用者的第一个参数取引用或解引用.
  - 字段访问在`->`之后加括号: `(x->0).0` (`x->0.0`读作浮点数).
  - proof函数的结果是spec值时 (`-> (res: Seq<..>)`, 没有`tracked`) 表记`(ret-ghost)`; client写成`let ghost mut r: T = arbitrary(); proof { r = f(..); }`, 不能`let tracked`.
- **类型和方法按名字解析.** 表中类型写最后一段, 由client的import解析 (ostd的全路径常经过私有模块). ostd的trait也一样 (2026-11-22): 以前写定义处的路径 (`<Frame<M> as crate::sync::rcu::non_null::NonNullPtr>`), vostd `eb1a9d044`把`sync::rcu`改为私有之后是E0603, 而rustc对限定路径中的trait不给经重新导出的建议, 修补无从下手 (`frame_ref`的6个条目). 现在写`<Frame<M> as NonNullPtr>`, 由模块自己的`use`或rustc建议的导入解析; ostd的trait名字互不相同 (`eb1a9d044`有135个). 有几个同名类型时 (vstd的`simple_pptr::PointsTo`, `cell::pcell_maybe_uninit::PointsTo`, vstd_extra的`array_ptr::PointsTo`), 解析到的不是要的那个 (E0107); 抽取器对ostd和标准库以外的同名类型带上模块并import它. trait方法的self类型有同名的固有方法时 (`<Frame<M> as NonNullPtr>::into_raw`与`Frame::into_raw`, `DmaCoherent`的`daddr`/`paddr`), 方法调用解析到固有方法, 探针于是报requires-weaker (固有方法的requires); 这样的条目写成`<Self as Trait>::name`. 曾经为此给表加了固有方法的requires, 那是把表的requires加强了. 类型参数上的关联类型写`M::ReprPerm`; trait有类型实参而实参不含类型参数时写`<M as Repr<MetaSlotStorage>>::ReprPerm`: 协议的两个API使M有两个`Repr<..>`约束时, `M::ReprPerm`有歧义 (E0221). 关联类型上的约束不检查 (表中没有), 所以要求trait约束的类型参数不实例化为关联类型 (`raw_as_ref`返回的`Either<L::Ref, R::Ref>`上的`into_raw`).
- 私有字段不能出现在公开函数的ensures中 (修改`FrameAllocOptions::zeroed`的ensures时被Verus拒绝).
- 闭包的规格只经`call_ensures`转发: `wait_until(|| self.try_lock())`中闭包没有ensures, `lock`就什么也得不到.
- trait的默认`ensures`不适用于覆盖它的实现.
- **VIR的格式随Verus变.** Verus `84ae63ed` (2026-10-28之后的"Fix DefId -> Path collisions") 的路径每段带命名空间 (`t%mm`, `tdis<N>%NAME`, `vdis<N>%NAME`); 读VIR时去掉, 其余部分看到的仍是旧的形式. 换Verus后先核对VIR打印的代码 (`source/vir/src/ast.rs`, `printer.rs`) 的diff.
- **Verus生成的项不是API.** Verus `5ef50d52` (2026-11, "Handle auto-derive clone for non-Copy types") 为派生的`Clone`生成`vdis%N%clone_clause_autoderived%`函数; 名字去掉命名空间和继承的默认方法的改写 (`default%impl&%N%%%m`) 之后仍含`%`的项, Rust写不出它的名字, 不进表. 第一次在`eb1a9d044`上建表时, 它们在6个模块中进了表, 每个都是解析错误 (`expected ,`); 解析错误使整个模块的探针编译不过, 探针的修补轮次用在一个一个地去掉它们上, `mm.page_prop`于是152个条目全部`not-verified` (2026-11-22).
- **关联常量经self类型写.** vostd `4676a774b` ("Associated Const") 之后, 子句中的常量可以是impl的关联常量 (bitflags的`PageFlags::AVAIL1`, 在spec中是`AVAIL1_SPEC`), VIR的路径是`ostd::mm::page_prop::impl&%26::AVAIL1_SPEC`. 照关联函数的规则 (`current-impl-path`) 写成`PageFlags::AVAIL1_SPEC`; 写不出时 (泛型impl的类型实参不知道) 这条子句不能由VIR写回, 同其他`fail`. 以前直接写成`crate::mm::page_prop::impl&%26::AVAIL1_SPEC`, 一个解析错误, 同上使整个模块编译不过. trait的关联常量 (`PagingConstsTrait::NR_LEVELS`, 以前是函数`NR_LEVELS()`) 在VIR中是没有实参的调用, 被调用者的`item_kind`是`Const`: 写成`<C as PagingConstsTrait>::NR_LEVELS`, 不加`()` (E0618).
- **VIR中跨度的行号可能偏.** 在声明了client模块的检出上导出的VIR, 模块文件中多一行声明, 其后的跨度都偏一行. 由跨度找源码时, 取跨度起点附近最近的`fn NAME`; 宏生成的函数 (`arrow_1`) 没有这样的行, 只能用跨度本身. 导出VIR前先确认检出是干净的.
- **`#[verus_spec(..)]`中有`#[trigger]`.** 由源码向上取属性时要数括号; 把以`#[`开头的行一律当作属性的开头, 会在`#[trigger]`处截断.
- **类型就是`Tracked<T>`的参数** (proof函数中, 而不是`Tracked(x): Tracked<T>`的绑定) 在元组中不要再包`Tracked(..)`; 对`Tracked`字段做变体检查 (`is Some`) 时要取视图`@`. 这两处抽取的错误使`kspace`和`vm_space`的12个`PageTableConfig`引理和`node::lock`编译不过.

### 4.3 表示和数据

- 表绑定在vostd提交上 (3.2). vostd更新很快; 更新后要重新抽取, 探针, 与旧提交的探针逐个条目比较, 并看新旧提交上的签名和requires (表的requires比源码强时探针发现不了).
- **存档的中间结果可能早于工具的改动.** 旧的探针结果是在抽取的一次修改之前跑的, 那次修改的bug因此一直没暴露, 换提交重新抽取时才出现. 拿旧结果作基线之前, 确认它是用当前的工具跑出的; 否则重跑.
- 不要直接编辑抽取出的表或机械修补的覆盖表: 重新抽取会覆盖它们; 人工的修补写在单独的覆盖表中.
- 补丁文件要核对内容再用: 一次shell命令出错, 使"合并后的补丁"没有替换旧的, 而报告已经按合并后的写了; 打补丁评估时只覆盖了一半的修改, 直到某个模块的结果与预期不符才发现. 用之前看它改了哪些文件 (`git apply --stat`), 与报告对照.
- 续跑的结果必须绑定检出的状态 (提交和改动), 否则打了补丁的运行会重用没打补丁时的结果.
- 知识文件中的API名必须是表中的名字; 协议中引用表外的函数 (私有的, 带闭包) 时这个协议不能用, 检查时报出.
- 按字符位置剪切文件时注意CRLF (Racket开了行计数后把CRLF算作一个位置). 编辑前备份.

### 4.4 规模

- client数由分支 (else, 值条件) 和实参选择决定: 一个协议在允许中间插入任意调用时耗尽内存, 把参数取为各调用探针参数的并时有50万个client. 每一族都要有预算.
- 在一个模块中按深度降级 (超过上限时降低深度), 降级要写进结果.
- **生成的时间也要按协议的长度看.** 2026-11-11并入上一轮的知识后, vm_space多了几个8–13次调用的协议 (`ktest-map-twice`, `fork-cow-copy`), 生成从32秒变成54分钟. 协议的参数是各次调用探针参数的并, 三次`cursor_mut`就有三份`guard`, `va`, `owner`, `regions`; 每个参数的候选随前面调用产生的值增加. 测量的结果 (逐个协议计时, 再采样): (1) 实参组合先造出全部的积再按"可互换的新参数按声明次序用" (`canonical-combo?`) 过滤, 几乎全被丢掉; 改为逐个参数构造, 被拒绝的前缀不再延长 (`canonical-combos`), 生成的client逐字不变, vm_space的生成54分钟→7.5分钟. (2) 剩下的时间在`ktest-map-twice`一个协议, 每多一次调用翻一倍: 搜索的结点只有几十个, 但每一步对协议中每个API都把它的全部实参组合展开 (建立调用, 良构性检查), 再由性质判死; 不该在这一步调用的API全部试完 (max-choices凑不满). 把组合改成惰性的流不改变这一点 (试过, 没有加速). 于是在展开之前先由性质判断这个API能不能是下一次调用 (`prop.rkt`的`properties-may-call?`): 只看不带变量且字母不看角色的性质 (协议和chain的都是), 对它们一个事件是否匹配只取决于API的名字, 所以把历史接上"至多k次提供者 (每个tracked参数一次, 任意次序), 再一次这个API"就能判定, 与调用之后`properties-status`的结论相同, 不是近似. 35个模块的client逐项不变, vm_space的生成7分钟→78秒 (`ktest-map-twice` 6分钟→25秒). 剩下的时间仍随长度增长 (每两次调用约翻一倍), 在被接受的调用的展开中 (`bind-call`, 良构性检查; 5.4).
- 一个模块的验证从十几秒到几分钟; 全部34个模块约一小时.

### 4.5 环境 (Windows)

- shell的heredoc会把反斜杠减半; 含反斜杠的脚本用文件写.
- `python`的编辑会改变行尾; vostd的源码是CRLF, 编辑要保持.
- 不要在用户的vostd工作区中改动; 用专用的检出. 每次结束都检查检出是干净的.
- 验证可能改写检出中的`Cargo.lock`, 运行后恢复.
- 换了Verus就换构建目录 (`CARGO_TARGET_DIR`): 旧Verus编出的产物会混进来.
- 编译Verus时并行的rustc可能耗尽可提交内存 (页面文件在快满的C盘上不能增长): 症状是`os error 1455` (页面文件太小) 和随之而来的`only metadata stub found for rlib dependency core`等假的错误. 用`CARGO_BUILD_JOBS`限制并行.
- 新版Verus的`cargo dv bootstrap`把`cargo-verus`, `rust_verify`, `verus`, `cargo-make`装进全局的`~/.cargo/bin`; 不要动别处共用的Verus, 从它的仓库另建worktree再bootstrap.
- 在WSL中运行全部 (检出, Verus, target目录, Racket) 可以避开上面大部分问题 (路径长度, z3脚本的执行策略, rustup的`PATH`次序, 误报). 从Windows调用时: Git Bash会改写传给`wsl.exe`的`/mnt/..`, `/root/..`路径, 先设`MSYS_NO_PATHCONV=1`; PowerShell的引号和`$`会弄坏bash命令, 把命令写进`.sh`再调用. 7.7 GB内存下`CARGO_BUILD_JOBS=4`够用.
- 选`git`: 在WSL中`PATH`后面接着Windows的`PATH`, 先找`git.exe`会找到Windows的git, 它看不到`/root/..`, 于是HEAD为空串, 而空串是任何提交的前缀, 表与检出的版本检查就被悄悄绕过. 所以只在Windows上找`git.exe` (git.rkt), 并且HEAD为空时报错.
- 同一个仓库目录既在Windows又在WSL中用Racket时, 两边的编译产物 (`compiled/`) 互相覆盖 (`fasl-read: incompatible fasl-object machine-type`). 一边改用另一个编译目录, 例如在Windows上`PLTCOMPILEDROOTS="compiled/win;"`.

### 4.6 比较

- **逐个client比较, 不看总数.** 两次运行按client名字比较状态, 每个变化都要解释. 汇总数字会掩盖: 一条过宽的规则丢了几百条通过的链, 总数上几乎看不出 (3.3).
- **名字中的哈希不只由调用序列决定**, 同一序列可能改名; 改名而状态相同的, 按调用序列 (`source`) 对上.
- **通过的变多不等于更好.** 协议全用新参数时, 新参数的requires被提升, 什么也没检验却"通过"了 (原型中`sync.rcu`的协议16/16). 改成接着用前面调用的结果后, 通过的反而变少, 暴露出生成器的下一层问题 (owner的配对, 生命周期, 约束的合并, 导入); 逐个看才找得到.
- **一次只改一层, 改完就比较.** 同时换提交, 改工具, 改知识, 结果的变化就无法归因.

## 5. 目前的缺陷

### 5.1 合成

- **协议的构造有噪音.** 协议的参数是各调用探针参数的并; 枚举每步只留两个延续时, 先取到的是新参数而不是前面调用产生的对象, 新参数的requires在`regions`已被动用后提升不了, 造成假失败 (重新评估中74组协议失败有60组是这样). 现在协议的枚举先取调用产生的值 (`prefer-produced`), 其次用提供者从前面调用的返回值中取, 新参数只作后备; 真实代码中来自别的模块 (分配器) 的对象仍要靠那个模块的表在协议中出现.
- **协议中对象和owner的配对**已按来源修好 (`pair-by-origin`, 3.5); 序列中没有调用产生的owner不再与产生的对象拴在一起 (`consistent-fresh`, 3.5); 跨模块的名字由rustc的导入建议补上 (3.8); 共享借用使可变的借用者失效 (3.3). 剩下的协议噪音是: 对象本来不由序列产生 (分配器, 页表的owner, 不在表中), 少数类型不符.
- 返回元组的API的分量不能分别流向后面的调用 (`into_raw`返回指针和权限), `Err`的载荷用不上: 已改 (3.1, 结果的结构). 仍不解开的: `Ok`/`Some`中的元组, `Err`中的元组 (`(Error, usize)`).
- **在局部的guard上调用`get`做不到** (要高阶约束, 3.3): 协议中的`get`用新参数.
- **省略的生命周期`'_`默认关闭** (3.5): 打开会使一些模块的client数成倍增长; 关闭时从`new`出发的链调用不了`lock`, `reader`, `writer`.
- 抽取器不抽lemma的`ensures`: 已改 (2026-11-12, representation.md 6.8). 只抽"只有spec参数, 没有结果"的proof函数 (295个, 其中235个有可翻译的ensures), 标`(lemma)`; 有结果或tracked参数的proof函数不抽 (要快照和结果的名字).
- **`assume`只加在种子调用上**, 后续调用的饱和仍是噪音.
- **关联类型的若干签名编译不过** (`either`中10个).
- **闭包参数** (高阶API, 如`protect_next`) 只有设计, 未实现.
- **并发**不在范围内: 只有单线程的client; 锁的值没有模型时连"写后读到新值"都写不出.
- **循环**只能手写, 不枚举.

### 5.2 判定的辅助

- 空洞性检查只在路径末尾; 两条路径共用一条末尾断言时, 其中一条空洞发现不了.
- 连锁失败只按路径上的先后标出 (3.9), 不知道因果: `(first 0)`的组也可能有独立的缺陷, 修好前面的之后要重跑再看.
- 标签的准确率没有评估.
- 失败的协议没有专门的分组方式 (要区分构造的噪音与真实的缺口).

### 5.3 可信性

- 合成器只检查规格"够不够用". 可信代码的判定由人或LLM做 (3.12); 机械的只有列举, 漂移的核对和演示的运行.
- 子代理 (LLM) 的判定和重跑没有统一的复核流程; 目前靠人抽查.
- 调用知识的人工核对没有逐条的记录: 哪些条目经过人看过, 只能从改动和漂移的报告推知. 失败的claim中有相当一部分是claim本身写错了.

### 5.4 实现

- Verus输出的解析依赖文本格式.
- 长协议 (十几次调用) 的生成仍随长度增长 (4.4): max-choices的循环在一个选择后面走不通时试下一个, 每个都重新展开后面的调用; vm_space的`ktest-map-twice`一个协议要约25秒.
- 生成器的核心 (良构性规则, 渲染, 枚举, 探针, goal, 用知识的族) 没有离线的测试: 要用真实的表跑评估, 改动前后逐个client比较. 崩溃拆分和续跑也一样 (要Verus); 用两个模块的小配置做冒烟评估检查.
- 可信代码: 判定的指纹不含trait声明中的规格; 判定一致与否只比判定的类别, 不比理由; 范围外的可信代码 (`trusted`列出而没有区域覆盖的) 不会被报告为未判定.
- 版本的检查只比较提交, 不看检出中未提交的改动 (打了补丁的检出与原版同一个提交); 续跑的键看改动 (`pipeline/evaluate.rkt`), 表的检查不看. 对打了补丁的检出跑时, 表仍是原版的表, 这是有意的.
- 更新vostd的各步 (导出VIR, 扫描, 逐个条目比较, 指纹, 知识的检查) 还没有串成一条命令; 约每周一次, 按evaluation.md第3节手工做.
- **ostd自己的同名类型** 仍只写最后一段: 全路径常经过私有模块 (E0603), 而rustc的导入建议只给可见的路径. 抽取器只对ostd和标准库以外的同名类型带模块; ostd内部的冲突现在没有实例, 出现时要改抽取器 (本版没有手写的覆盖表).
- **不在`verus!`中声明的枚举没有`->`** (`util::either::Either`): Verus只为`verus!`中的枚举生成`arrow_`访问函数, `is`则都可用. 表中看不出一个枚举是否在`verus!`中, `knowledge`也查不出; 写claim时用`r matches Either::Left(x) && P(x)`, 不用`r->Left_0` (一条claim因此编译不过, 已改).
- **`--expand-errors`只展开每个函数中第一个失败的断言.** 同一client中后面的不透明子句的失败没有展开, 仍按子句的文本分组; 它们在第一个失败之后, 本来也要修好前面的再看.
- **要幽灵交接的协议不生成.** `cursor_mut_at`得到Some时链表的owner移进了CursorOwner, 调用者要`*owner = co.list_own`才能继续用链表; `cursor_front_mut`/`cursor_back_mut`不返回CursorOwner, 真实调用者由LinkedListOwner做一次幽灵的转换. 生成器不知道这些转换: 以前用无关的owner生成, 只会失败; 现在这一步不走, 这样的协议不出现在结果中. 要测它们得手写client (evaluation.md 5.1).
- **`DebugSpec::fmt_req`**: vstd对锁的guard类型没有给出`fmt_req`成立的条件, `fmt`的flow在这里失败; 这不是ostd的规格的问题, 判为不是缺陷.
- 生命周期仍是近似 (一个`'a`): client的共享引用参数写成`&'a T`, 结果借用由`no-flow`修正; 两个独立的生命周期都要的签名表达不了.
- **requires中有`match`, 闭包, 非布尔的`if`的条目** 这些子句VIR的翻译和源码的树都翻译不了, 现在保留为源码文本的模板 (3.2); 2026-11-12以前记为`(skipped-requires ..)`, 条目于是`requires-weaker`. 量词 (`forall`/`exists`, 规格表达式的`(forall ((i int) ..) E)`, 渲染为`forall|i: int| E`: 源码的触发器保留 (`#[trigger] e`, `#![trigger ..]`, `#![auto]`), 源码没有时写`#![auto]`; 只写`#![auto]`时Verus在源码标了触发器的地方推断不出 (could not automatically infer triggers), 整个模块编译不过), spec的`let`块 (代入) 和布尔的`if` (两条蕴含) 现在都抽取; 有名字段的结构体字面量 (`MappedItem { frame: frame, prop: prop }`, 规格表达式的`(record "PATH" ("f" E) ..)`) 也抽取. 模板只能代入和渲染: 提升, 求变量都只看洞, 不看其中的结构 (`match`的分支, 闭包).
- **claim要的额外约束.** claim的文本用到的spec方法可能来自约束更多的impl (`DmaStreamSlice::inv`要`M: OwnerOf`, 而`stream`的impl没有): claim client没有这个约束, 编译不过 (E0599). 生成器不分析claim文本中的方法, 写claim时只用API自己的impl能用的函数.
- **中断运行会留下client模块.** 被杀掉的运行 (kill, 关机) 来不及删去client模块和还原模块声明; 下一次运行开始时清理 (run.rkt的`clean-leftovers`: 未跟踪的`cs_clients.rs`, 唯一改动是`mod cs_clients;`的文件), 用户别的改动不动. `Cargo.lock`由`evaluate`恢复.
