# B23 Full004 论文条款与量词语义审阅

结论：**本次有界只读审阅通过；未发现 RootPaper_B23_Full004 与论文 price-proofs.tex:294–300 之间需要另补的实质算法、量词、资源或费用缺口。** 该结论是下面列明范围的语义审阅，不是重新编译、source/product 验证或全篇 S7 验收。

原文通过 `rg --files -g price-proofs.tex` 定位。读取工作稿 [submission 原文:294](D:/STOC投稿/compatibility_structure_research/submission_2026-10-27/manuscript/sections/price-proofs.tex:294) 及其 261–300 行，并对照 [冻结稿:294](D:/STOC投稿/paper_writing_bundle_2026-11-01/paper_frozen_2026-10-29/manuscript/sections/price-proofs.tex:294)。两稿 294–300 行内容一致：posterior odds 使用有理产品和有理边界；threshold/quota 用整数比较及有理算术；计算成本依赖输入位长与数值 call quotas，不主张 poly(log H)；不足的固定 caps 返回 sufficient check 失败，不扩大原合同资源。

审阅对象是 [Full004:31](D:/STOC投稿/lean/.lake/workpads/Structure/RootPaper_B23_Full004.lean:31) 的新 paper-aligned 三部分声明及 [full_paper_claims:116](D:/STOC投稿/lean/.lake/workpads/Structure/RootPaper_B23_Full004.lean:116)，没有将其解释为旧强化 Bool-machine Claims 的证明，也没有提出新的编译器、parser、ISA 或输出格式目标。

| 核对项 | 具体连接与结论 |
| --- | --- |
| 原数值 quota 与尺度 | [ReferenceCertification:44](D:/STOC投稿/lean/PaperProofs/Common/ReferenceCertification.lean:44) 的 `ReferenceRiskChoice` 保留原 real-delta 最小 dyadic exponent，且 `quotaExponent budget N = exponent`，不是另给运行时 E/Q 答案。Full004 的 Core 和 `qualifiedResources` 保留原 drift/channel/prior/quota 四字段。[RCC:207](D:/STOC投稿/lean/PaperProofs/Common/RationalControllerComputation.lean:207) 中 `numericalQuota` 是 computedQuotas 的数值和；`inputSize` 是原 preparationInput 位长加 N、q 和 1；`arithmeticScale = inputSize + numericalQuota + 1`。Full004 未改尺度，未声称 literal-bit-only 或 poly(log H)。 |
| qualification=false 与原合同 | `PreparationPaperClaims` 对所有原 I/input/C、任意正 Rat budget 成立，没有 true qualification 前提；第 37 行直接给计算所得 Bool 等于原 `numericQualification`。因此原检查 false 时结果确为 false。Native/统计部分仅在原 `ReferenceCompleteOriginalQualification` 下构造实际 policy；并未把数值 Bool 反向当作 H0 证明，也未制造扩大资源的 C。 |
| 同一个原 policy、所有样本和失败路径 | [ExecutedReference:45](D:/STOC投稿/lean/.lake/workpads/Structure/RootPaper_B23_Full004.lean:45) 中 policy 是同一个显式 `completeNativeReferencePolicy`，其 Core 包含 same_rule、所有 sample/clock 的 same_run、normal-call certificate 和原 caps。Full004 第 51–59 行联合给该 policy 实际 native history 上的动作等式、停机与所有 sample 的完整计算费用，没有成功事件或另供 Prefix 前提。[Ordinary024:32](D:/STOC投稿/lean/.lake/workpads/Structure/RootPaper_Reference_Ordinary024.lean:32) 在内部用 Core 和 run_has_prefix 消去局部 Prefix 条件。 |
| 固定 strong WORD runtime 的量词 | [FullPaperClaims:87](D:/STOC投稿/lean/.lake/workpads/Structure/RootPaper_B23_Full004.lean:87) 在全部 I/input/C 等量词之前只选一次 `runtime`；证明通过 `wordRuntime_exists` 构造它，而非留作 caller 的假设。[Fees020:18](D:/STOC投稿/lean/.lake/workpads/Structure/RootPaper_Reference_Fees020.lean:18) 的 WordRuntime 同时固定 states/code/port/coefficient/degree，并对所有原 E、任意 Rat target、StoppedWord 给实际 Runs、同 port、真实 HALT、原 wordOutput、输入/输出复制费及所有 trace prefix 的 visitedSpace 界。后续 wordFeeFor/word_realized 始终消费同一个 runtime，没有逐 WORD 另选 code。 |
| 准备一次与 single-F 总费用 | [NativeCost023:17](D:/STOC投稿/lean/.lake/workpads/Structure/RootPaper_Reference_NativeCost023.lean:17) 的 prepareOnce 捕获实际 preparationCalculation.value.rows 的 quota getter。[totalRunningCost:92](D:/STOC投稿/lean/.lake/workpads/Structure/RootPaper_Reference_NativeCost023.lean:92) 在时钟求和外只加一次 Prep.runningCost，后续用捕获的 initialized controller；Full004 直接采用该总费，未再次加准备费。其界只有一次 `generalStructureFactor I * globalRate runtime * arithmeticScale^globalDegree runtime`。该 F 仍是原 general-graph 结构因子，未称作多项式结构算法；globalRate/globalDegree 只依赖预先固定 runtime。 |
| halt horizon 确实覆盖全部实际计算 | [ControlBits021:197](D:/STOC投稿/lean/.lake/workpads/Structure/RootPaper_Reference_ControlBits021.lean:197) 定义 `originalHorizon = quotaActionBound I (computedQuotas input budget)+1`。[Full004:92](D:/STOC投稿/lean/.lake/workpads/Structure/RootPaper_B23_Full004.lean:92) 用 Core 的 same exponent 精确改写为 `quotaActionBound I (referenceQuota input exponent)+1`，第 105–107 行直接接 Core.halted。总费求和范围是 clock < originalHorizon，覆盖导致 horizon 时刻停机的最后一次实际控制动作；已 halted 的项为零，不收费于实际停机后的虚拟继续时钟。不存在另给 horizon/fuel 的 caller 前提。 |
| full-set risk 与 full expectedBill 的准确域 | [StatisticalPaperClaims:72](D:/STOC投稿/lean/.lake/workpads/Structure/RootPaper_B23_Full004.lean:72) 明确保留 0<delta≤1/2，并仅针对 `I.tools` 的原完整资格证书给统计比较。结果是同一个 ExecutedReference policy 的 risk≤delta 与 native expectedBill≤原 uncapped ideal expectedBill；未推广到任意 available，未换成 normal-call-only 账单，未增加成功条件。[NativeExecution:145](D:/STOC投稿/lean/PaperProofs/Common/NativeExecution.lean:145) 的 runActualBill 是所有前缀 ledger.actualBill 的上确界；[expectedBill:182](D:/STOC投稿/lean/PaperProofs/Common/NativeExecution.lean:182) 在全 seededWorldLaw 上积分，不按 runSuccess 截断。因此包括最终失败路径上已发生的费用。 |

几个容易误读、但本次没有发现遗漏的边界：

- `ReferenceRiskChoice` 是原 rational-risk 接口的证明条件，不是运行时 quota、宽度、成本或 KL oracle。已有 [exists_referenceRiskChoice:52](D:/STOC投稿/lean/PaperProofs/Common/ReferenceCertification.lean:52) 在原正 N/正 delta 小风险域给相同原 exponent 的 rational budget；Full004 的准备算法仍自己计算 exponent 和 rows。
- `PreparationPaperClaims` 的统一 c/d 在所有原输入之前；实际 controller 总费使用 NativeCost023 已联合证明的 preparationRate/globalRate，而非从一个输出长度界推断运行成本。
- 算法的 `totalRunningCost` 与合同货币账 `expectedBill` 是不同量。Full004 同时保留二者，未把计算费用改记为原 observation/correction prices，也未删去失败样本费用。
- `qualifiedResources` 是被证明等于实际准备结果的规格记录。Full004 第 103 行以 initialize_value、original_rows、Core.exponent_eq 与 Core.numeric_check 识别它；它不是新 caller input。
- 同一原 policy 上的动作连接是所有 sample/clock 的结果；不再要求最终 caller 提供合法 history、Prefix、预计算 getter 答案或运行成本证书。

本次读取了 Full004、最短 API 笔记，以及为上述具体核对所需的 Core001、Prep_Ordinary008、B23_Preparation002 的资源记录部分、Reference_Ordinary024、Fees020、NativeCost023、ControlBits021 的 horizon 定义、RCC 的尺度定义、ReferenceCertification 的 risk-choice/资格定义、GeneralNormalFeeReference 的同 policy/performance 接口、NativeExecution 的 run/risk/actual bill/expectedBill 定义。没有启动旧父审计，没有复验 Reference144 pins，没有编译、hash、修改任何 Lean source、forwarder 或正式配置。

状态另据 Root 本轮明确回报记录：Full004 strict001（outer81633）、Ordinary005（outer38602）、Audit006（outer51114）已 actual0、回收并分别独立冻结六项；新增 owner ALL 为 2 modules / 15 declarations / 10 theorems / 5 definitions / private0 / new axioms0 / forbidden0，记录为 `ROOT_PAPER_B23_FULL_THEOREM_STAGE_REVIEW_20261102_001.json`。Reference 也已由 Root 验收，第五 producer 完成，producer 为 5/5。此段是 Root 状态回报的引用，不是本审阅重新执行或核验其字节/收据。

**正式仍 251/253，工程绑定及 S7 尚未完成。** 本审阅没有据此推进正式主账，也没有新增数学证明任务。
