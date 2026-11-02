# PA06 原主链及 A06 范围预审 001

记录 UTC：2026-10-30T05:27:17.319876+00:00；新总协调 `01a18842-1cab-7ae3-92b2-24c2adf72528`。本次仅做有边界只读预审，旧全局goal保持暂停，不接管正式集成。读真实冻结原文、原目标和最终证明；只写 PA06_SCOPE_*，没有启动 Lean/Lake/文档编译、全工程验证、公理审计或更改任何正式文件。

## 结论

本次已检查的 B08、获准 first-entry B09、B11/B12、B24/M08 及 A06 原目标，未发现需要撤销其“已闭合”登记的范围/量词/比较器缺口。该结论不等于全部源码逐行重审，也不等于 S7 全篇验收通过。当前新Root正在正式集成其他交付；私有complete一律不提前增正式闭合数。本次新增闭合数为0。

B08/B09/B11/B12的原文行、确切目标与实际证明链、源码SHA见 `PA06_SCOPE_MAINCHAIN.md`，本父审查已复核该产物。其关键核查：独立全策略 ENNReal infimum而非递推定义；任意Seed同值编码；local/good/bad三个epsilon见证而非最优取得；真实首次进入与旧宽反例隔离；严格 N−next 后缀归纳只消费 next+1，局部 cancellation 不回用全局 B11。

## B24 原固定图价格：比较器与量词

冻结原文 `manuscript/sections/prices.tex:4–18,40–64`：图/顺序/先验/channel/观察及修正价先固定，只有delta和合资格原contract可变；full history、private randomness、non-MAP、legal delay、abandon、拒绝修正和失败后继续付费均在比较器内。下界不需要资源证书；证书用于matching native upper。:49–57任意初始R的ordered coefficient另由B14覆盖，不把FixedGraphPriceLaw自身仅all-tools初始态的包装误称all-R新结论。

- `Common/NativeExecution.lean:178–199`：risk是完整runSuccess反面，expectedBill是实际账单的非负积分；`value`为同input/contract/mode/accounting下δ-safe真实合法Policy的inf，不是Bellman递推。失败路径及无限期望不删。`NativeSeed.lean:172–181,190–末` 对任意 Seed 宇宙保原risk/bill同值压缩；`NativePartial.lean:258–266` 覆盖原partial不返回策略，已付费不归零。
- `Common/PenaltyAsymptotics.lean:86–94` 的 `NativeLowerPriceLaw` 是 input固定后：∀finite depth→∀epsilon>0→∃delta0>0→∀small delta→∀current-allocation C/accounting 的ENNR Native.value下界；没有 H0/finite-cost/MAP/终止限定。
- `Common/HealthyPriceClosure.lean:19–25` 的 `nativeLowerPriceLaw input` 真实用已证 `input.penaltyAsymptotics` 消去条件；`fixedGraphPriceLaw input` 直接返回原 `FixedGraphPriceLaw`。原条件adapter仍保留但不是最终证明的额外前提。
- `Common/ReferenceCertification.lean:374–397` 的 upper及∞rank目标明确要求原THIS-reference资格；input与epsilon cutoff先于delta/caps/accounting。∞rank还要求实际native policy、零risk/零observation，以及真实correction bill≤min(N,q)*maxCorrection。
- `Common/ReferenceSharpNativeUpper.lean:65–108` 真实调用已证 referenceCostAsymptotics、同指数有理budget选择、原风险/overflow/截断/native迁移；没有 hcost/hrisk 等待证性能参数。:111–末直接构造 bounded.enforceCaps，逐sample/clock同run，运输零risk/零observ及actual correction bound。
- `Common/FixedGraphPriceAssembly.lean:17–23` 将 lower、nativeUpperPriceLaw、nativeInfiniteRankPriceLaw及正coefficient拼成原包；`HealthyPriceClosure`已给lower。因此“编译了一个带目标前提的定理”不是现有B24状态。
- B14的真实入口 `Statistics/Coefficient.lean:179–209`、`Common.StatisticalInput.orderedCoefficient_head_formula` 对任意remaining R给有序head表达；系数正性见同文件:241–245。不是把系数直接定义成未经核对的递推答案。

**边界：**B24 是数学统计价格law，不证明B23独立Bool TM、A19原raw packed controller或L01实际table tie的所有计算/资源字段。THIS-reference资格不能自动转嫁给retained/star/不同tie脚本。

## M08 / B21：原 H0 未偷偷变成比较器限制

冻结 `model.tex:35–55` 允许更大合法策略类并要求所有失败费计入；原 normal fee C0 与 variable bill分开。`price-proofs.tex:277–292` 要求本构造的实际Qhat和ordinary操作合法，原 H≥H0+ΣQhat+min(N,q)，overflow abandon只删未来非负费用。

- `Common/ReferenceCertification.lean:62–69` 的 ReferenceOriginalQualification只含原stage quota、原total cap和这个具体 `referenceBoundedPolicy` 的 H0证书，未对所有comparison policies加H0。
- `Common/NormalResourceClaims.lean:44–53` 的 `ReferenceCompleteOriginalQualification` 第三个字段是原complete-execution H0；:56–69证明与已有all-prefix资格等价。:104–116的最终 `referenceCompleteResourceClaims`/`normalResourceClaims` 返回实际native Policy，同rule/同所有run，并覆盖每个sample/prefix的合法计数/原caps/≤min(N,q)修正。
- 等价不是把待证上界当“数值自动成立”：`Common/BoundedNormalIO.lean:68–81`由真实quota/once-only ports/tools得halt；:114–145 normalCalls单调，完成时界覆盖所有较早前缀；:147–170对这个具体bounded rule实例化，不用成功条件。CompletedNormalCallBound:124–128 包含全部halt（失败/abandon也包括）。
- 没有从任意NormalAccounting捏造H0，也没给任何input平台声明“所有adapter都自动满足”。这是原稿的选定脚本资格，M08b普通证书定义本身不等于所有脚本证书已证。

未发现M08闭合所依赖的额外未授权资源假设。实际平台I/O成本/THIS-table及不同合同脚本资格仍归各自原目标，不能以generic M08替代。

## A06：真正 raw 程序、输出和全成本

冻结 `laminar.tex:12–20,24–50` 及 `laminar-proofs.tex:235–243` 明确 explicit incidence、q>0构树/检查、去重/最小superset parent/children覆盖，O((N+q+1)^2q)；q0独立分支、N0/重复stage/unused tool边界见A:263–270。

- 原目标 `Structure/RawTreePreprocessingClaims.lean:98–113`：先∃constant/wordFactor/program，再∀q/full及原q>0；从且仅从 rawIncidenceROM + zero heap运行。所有nonLaminar输入也同界拒绝；接受才输出真TreeOutputCorrect。没有预给prepare/card/parent/rank/table/trace/safe假设。
- 最终 `RawTreePreprocessingA06Closure.fullClaims`（:57–58）真返回原目标，`prefixSafety`已被 `all_prefix_safe`（:22–55）证明；不是只调用仍带hsafety的adapter。接受路径Parent→443输入serializer→427children serializer→13footer→真实HALT全部同clock衔接；拒绝独立gate/HALT。停机后任意clock安全亦已包含。
- `RawTreePreprocessingWordInterface.lean:94–末` 具体constant262144/wordFactor16/fixed程序，利用Nat语义、完整prefix safety和真正first-halt拼成DynamicRunCorrect及实际输出；hword是同一first clock，不混用另一个理想输出状态。
- `RawTreePreprocessingNat.lean:181–202` 独立完成原Nat输入语义；固定2089-op/10450codewords，`CodeBounds.lean:26–39`；`CostBounds.lean:90–末` 的 totalCost包含真实ROM/code loading、heap zero初始化、8 registers、动态fetch/branch/access trace与encoded HALT。
- 实际heap输出逐字等于 `[region lengths] ++ givenTreeROM regions`，`readSerializedROM=givenTreeROM`，t≤N+q+1。prepareNormalization仅为输出规格，机器并不调用host Finset/mergeSort oracle。确切输出布局/元数据边界及复用签名见配套 `PA06_SCOPE_A06_A19_MAP_001.md`。
- q0没有塞入乘q=0的正q成本；`ControllerBoundaries.lean:99–111`为原q0 direct语义，N0在原正q全量词内。该边界不削弱冻结A06。

**未发现A06原范围缺口；但A06→A19仍需证明ROM尾部/active pre-HALT代码续接/实际heap→ROM或heap adapter/一个统一字宽/compact peak heap及全loading成本五项接口。**这不重开A06，也不把已闭合A06作为A19已实现的替身。

## 发现分类与交付

- 数学漏洞：本次指定关键链未发现。
- 原文省略但已有正式证明：epsilon非取得、history replay、局部等秩消去、完整H0→prefix及A06真实程序均已定位。
- 实现/表示接线：A06→A19五项，详见地图，不冒称是新定理或已证明反例。
- 文档时效：若干旧模块头仍写“Pending”“statement interface”“lower still pending”；原FullClaims/Price closure已在后导入模块证明。Root可在正式批次统一同步注释；本次不修改，不能据旧注释撤销闭合或重做数学。

本次静态证据与SHA另见 `PA06_SCOPE_MANIFEST_001.json`。当前正式主账/收据由Root唯一维护；本预审未复跑其验证，也不宣告其他刚交付私有目标正式完成。后续等待Root下一项有边界任务。
