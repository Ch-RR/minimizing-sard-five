# 五维 Minimizing Sard 定理

[English](README.md) · [论文全文 · 21 页](paper/minimizing-sard-five.pdf) · [逐条复核 · 8 页](audit/minimizing-sard-five-audit.pdf) · [Lean 主定理](lean/FiveDimensionalMinimizingSard.lean#L75)

想象一辆每个位置只能朝某些方向移动的小车。固定出发点，选一条到达目标的最短路线，再给驾驶动作施加微小扰动。如果终点的一阶变化始终漏掉某个方向，这条路线就叫作**奇异最短路**。

**定理说，在五维空间里，能够由至少一条奇异最短路到达的终点，合起来的五维体积为零。** “体积为零”允许有无穷多个终点，正如一条直线在平面里可以无限延伸而面积仍为零。每个出发点都有自己的例外集；一个终点即使也有普通最短路，只要有一条奇异最短路，就计入这个集合。

## 数学陈述

设 $M$ 是连通、Hausdorff、第二可数、无边界的五维光滑流形，$\Delta\subset TM$ 是光滑常秩、处处括号生成的分布，$0<\mathrm{rank}\,\Delta<5$，其上给定光滑正定内积。令 $E_x(\gamma)=\gamma(1)$ 为固定起点的水平 $W^{1,2}$ 路径空间上的终点映射。对每个 $x\in M$ 和每个光滑正密度 $\mu$，有

$$
\mu^*\!\left(\{y\in M:\exists\gamma,\ E_x(\gamma)=y,\ L(\gamma)=d(x,y),\ \operatorname{rank}D_\gamma E_x<5\}\right)=0.
$$

集合只计入实际达到最短长度的路径。流形可以在次黎曼距离下不完备。

## 如何阅读这条证明

Rifford 的定理 1.1 在完备性和几乎处处 Goh 秩至多为一的条件下证明了极小化 Sard 性质，其推论覆盖分布余秩为二的情形。在五维流形上，秩二分布的余秩为三。这份稿子处理任意光滑、常秩二、处处括号生成的五维情形，并允许括号生成空间的维数随位置变化。[Rifford，2023](https://doi.org/10.5802/jep.242)

| 想知道什么 | 从哪里读 |
| --- | --- |
| 为什么五维有机会？ | 论文第 4 节。最难分支的一阶导数只能覆盖三个方向；命题 4.4 在剩余二维空间中辨认出一条由李括号确定的直线。 |
| 怎样从一条路径推到一片终点？ | 第 5–6 节。先缩短路径，再估计修正终点的代价。命题 6.3 在选定任何路径之前先固定一个零测例外集。 |
| 怎样从一片下降区域推出零体积？ | 第 2 节。不同方向按不同速率缩放；把多个尺度的允许位移拼起来，再沿曲线使用一维测度结果。 |
| 纸面引理分别对应哪个 Lean 声明？ | [复核稿最后一页](audit/minimizing-sard-five-audit.pdf)。它也标明哪些纸面推广比主定理使用的形式化实例更广。 |

## 在自己的电脑上验证

需要 Git、[elan](https://github.com/leanprover/elan) 和 Python 3.8 或更高版本。从仓库根目录执行以下命令。首次运行需要联网下载 Lean 和 mathlib 缓存。

```sh
cd lean
lake update
lake exe cache get
lake env python check.py
```

如果你的系统使用命令 `python3`，最后一行改用 `lake env python3 check.py`。脚本核对 150 个模块的 SHA-256，按依赖顺序编译，运行内核重检，最后检查两个补充审计文件。[重检记录与口径](audit/README.md)

## 项目文件

- [paper/](paper/) 含论文 PDF、LaTeX 主文件及分节源码。
- [lean/](lean/) 含 Lean 4.24.0 证明、mathlib 版本配置和验证脚本。
- [audit/](audit/) 含独立复核稿、冻结版本的重检记录及其说明。

本项目使用 AI 辅助数学推导、形式化和写作。Lean 检查的对象是源码中的精确定理。若发现纸面陈述和形式化陈述有差异，欢迎在 Issue 中指出引理编号、Lean 声明和有疑问的推理步骤。
