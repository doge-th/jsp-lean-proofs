# JSP-000307 Lean 证明独立验证报告（提交前自查）

**总体结论：有条件通过。**
>
> 依 lean-verify skill 的结论表：全部目标检查成功、无证明缺口，但依赖明确可解释的扩展信任——`native_decide` 本机计算（对见证值 13, 7, 5 的求值）。若验收方不接受本机计算信任，结论降为待定而非完整通过。

在证明仓库 https://github.com/doge-th/jsp-lean-proofs 的 commit
`f3c2e369a58a4f9bff119e0c5b6e6b99f6ec1848` 上，该提交已**完整解决**指定原题
JSP-000307（"Can three consecutive integers have strictly decreasing largest
prime factors?"）：原题为纯存在性问题（∃ 三个连续正整数其最大素因子严格递减），
形式化定理以显式见证 n = 13 完整给出该存在性证明，全部目标检查通过、无证明缺口。
除标准公理外，见证判定使用了 `native_decide`（本机计算，信任范围见下）。

| 必答问题 | 明确判断 | 决定性依据 |
| --- | --- | --- |
| 证明对象是否就是指定原题？ | 是 | 原题即 "Can three consecutive integers have strictly decreasing largest prime factors?"，形式化定理 `JSP000307.jsp_000307_statement : ∃ n, lpf n > lpf (n+1) > lpf (n+2)`（lpf = Nat.maxPrimeFac）与原题逐一对应：存在量词、三个连续整数（n, n+1, n+2）、最大素因子、严格递减。无额外假设。 |
| 指定 commit 是否实际验证通过？ | 是 | 隔离环境全新克隆，`lake build` 退出码 0；官方 audit.py 逐目标检查（build + 源文件重查 + Audit 桥接文件 `#check`/`#print`/`#print axioms`）全部退出码 0。 |
| 是否完整解决原题？ | 是 | 原题为纯 ∃ 命题；见证 n=13（lpf(13)=13, lpf(14)=7, lpf(15)=5，经 `native_decide` 逐值判定）即完整证据，无剩余义务。 |
| 是否满足本次验证的 Lean 完整性要求？ | 满足 | `#print axioms` 输出仅 propext、Classical.choice、Quot.sound 与 `native_decide` 实现公理；无 `sorryAx`、无占位声明。 |

## 固定证据

- 验证时间：2026-09-25（UTC+8）；工具链 `leanprover/lean4:v4.35.0-rc1`（Lake 5.0.0-src+86c6347）。
- Lean 仓库：https://github.com/doge-th/jsp-lean-proofs，branch `main`，验证 commit `f3c2e369a58a4f9bff119e0c5b6e6b99f6ec1848`（= branch tip）。
- 原题来源：awards 仓库 `problems/catalog-0301-0400.md` JSP-000307 条目（问题措辞逐字核对）。
- 目标声明完全限定名：`JSP000307.jsp_000307_statement`；源文件 `proofs/JSP000307.lean`
  （SHA-256 `b5cafbda73927bc341d3d74e34ab5de0da79e91208bc69044c239e7fced78afa`）。
- 无版本冲突；无临时快照（验证 SHA = 提交者指定 commit）。

## 数学命题与覆盖

| 原题要求 | Lean 对应 | 覆盖 |
| --- | --- | --- |
| ∃ 三个连续正整数 | `∃ n : ℕ, …`（见证 n=13） | 全部 |
| 最大素因子 | `Nat.maxPrimeFac`（Mathlib 标准定义） | 全部 |
| 严格递减 lpf(n) > lpf(n+1) > lpf(n+2) | `>` 链，`native_decide` 判定 13 > 7 > 5 | 全部 |

无未覆盖子要求。

## 环境与执行

| 项目 | 值 |
| --- | --- |
| OS/架构 | macOS arm64（darwin 25.5.0） |
| 隔离方式 | 独立克隆目录 `/tmp/lv-final2/repo`，pinned commit 检出，工作区零修改 |
| 依赖 | mathlib `c32e1ec0d1eb`（lake-manifest 固定）；工具缓存复用（可信缓存，未改动源） |
| 构建 | `lake build JSP000307` — 退出码 0 |
| 目标检查 | audit.py run：9 命令全部退出码 0（build / 源文件检查 / Audit 桥接检查） |

## 证明完整性与可信边界

`#print axioms JSP000307.jsp_000307_statement` =
`[propext, Classical.choice, Quot.sound, JSP000307.jsp_000307_statement._native.native_decide.ax_1_1]`。

- 标准公理 propext / Classical.choice / Quot.sound：经典 Lean 基础，不计为缺口。
- `native_decide`：本机计算判定（对 `Nat.maxPrimeFac 13/14/15` 的具体求值）。
  按验收规则属**有条件通过**级别的扩展信任：信任 Lean 编译器与运行时对该
  有限计算的求值正确性。该信任范围已明确列明，非 `sorry`，非未证明假设。
- 无 `debug.skipKernelTC`、无元程序伪造、无 `implemented_by`/`extern` 依赖。

## 复核级别

已完成的复核级别：**实际 Lean 检查**（隔离环境、pinned commit、逐目标 build +
axiom 审计，官方 audit.py 执行，日志与 SHA-256 存档于
`verification/audit-f3c2e369/`）。未做 kernel replay 与外部 checker 独立复核——
native_decide 路径下 kernel replay 不适用，已如实记录。

本报告为提交者自查，不构成独立认证；以维护者复核为准。
