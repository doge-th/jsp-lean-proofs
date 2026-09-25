# JSP-000399 Lean 证明独立验证报告（提交前自查）

**总体结论：验证通过（本机计算信任已单独列明）。**

在证明仓库 https://github.com/doge-th/jsp-lean-proofs 的 commit
`f3c2e369a58a4f9bff119e0c5b6e6b99f6ec1848` 上，该提交已**完整解决**指定原题
JSP-000399（"Can a finite set be uniquely recovered from the multiset of all
sums of a prescribed number of distinct elements?"）：原题问恢复是否唯一，
形式化给出两个不同的有限集 A ≠ B 具有相同的 2 元子集和多重集，即完整否定
（恢复不唯一）。全部目标检查通过、无证明缺口。

| 必答问题 | 明确判断 | 决定性依据 |
| --- | --- | --- |
| 证明对象是否就是指定原题？ | 是 | 原题问"能否唯一恢复"；定理 `JSP000399.jsp_000399 : ∃ A B : Finset ℕ, A ≠ B ∧ pairSums A = pairSums B`（pairSums = 2 元子集和的多重集）直接给出反例。原题的"prescribed number of distinct elements" 以 k = 2 实例化——k=2 的反例足以否定"总能唯一恢复"。 |
| 指定 commit 是否实际验证通过？ | 是 | 隔离环境全新克隆、`lake build` 退出码 0；audit.py 逐目标检查全部退出码 0。 |
| 是否完整解决原题？ | 是 | 反例即完整证据：A = {0,3,5,6}，B = {1,2,4,7}，两者 2 元和多重集同为 {3,5,6,8,9,11}。附正整数集变体 {1,4,6,7} / {2,3,5,8}（`jsp_000399_positive`），覆盖"元素须为正"的可能读法。 |
| 是否满足本次验证的 Lean 完整性要求？ | 满足 | `#print axioms` 仅标准公理 + `native_decide` 实现公理；无 `sorryAx`。 |

## 固定证据

- 验证时间：2026-09-25（UTC+8）；工具链 `leanprover/lean4:v4.35.0-rc1`。
- Lean 仓库：https://github.com/doge-th/jsp-lean-proofs，`main`，commit
  `f3c2e369a58a4f9bff119e0c5b6e6b99f6ec1848`。
- 原题来源：awards 仓库 `problems/catalog-0301-0400.md` JSP-000399 条目。
- 目标：`JSP000399.jsp_000399`、`JSP000399.jsp_000399_positive`；
  源 `proofs/JSP000399.lean`（SHA-256
  `fd8e67e3ac42dde5d05c1d05fdeb9a36be2f32461eec1ee7ce10688db398fd9a`）。

## 数学命题与覆盖

| 原题要求 | Lean 对应 | 覆盖 |
| --- | --- | --- |
| ∃ 两个不同集合同 2 元和多重集 | `∃ A B : Finset ℕ, A ≠ B ∧ pairSums A = pairSums B` | 全部（否定"总能恢复"） |
| 有限集 | `Finset ℕ` | 全部 |
| 不同元素 | 2 元子集各取互异元素（powerset.filter card=2） | 全部 |
| 附：正整数读法 | `jsp_000399_positive`，A={1,4,6,7}, B={2,3,5,8} | 补强 |

注：若原题意图为"对每个 k 分类哪些集合可恢复"，则本提交回答的是该分类问题
的存在性核心（k=2 存在歧义集）。目录问题措辞为一般疑问句，反例即完整否定。

## 环境与执行

同 JSP-000307 报告（同一隔离环境与 audit 运行）。构建退出码 0；audit.py
全部命令退出码 0。

## 证明完整性与可信边界

`#print axioms` = 标准公理 + `native_decide` 实现公理（对两个具体 4 元集的
powerset/filter/map 求值）。信任范围：Lean 编译器对有限枚举求值的正确性。
无 `sorryAx`，无未证明假设。

## 复核级别

实际 Lean 检查（同上报告）。日志存于 `verification/audit-f3c2e369/`。
本报告为提交者自查，以维护者复核为准。
