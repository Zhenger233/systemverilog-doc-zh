# 6. 数据类型
## 6.1 概述
本章描述以下内容：
 - SystemVerilog 逻辑值和强度集
 - 线网声明
 - 单变量声明
 - 常量
 - 数据的范围和生命周期
 - 类型兼容性
 - 类型运算符和类型转换

## 6.2 数据类型和数据对象
SystemVerilog 区分对象和其数据类型。数据类型是一组值和可以对这些值执行的操作的集合。数据类型可用于声明数据对象或定义从其他数据类型构造的用户定义数据类型。数据对象是一个具有数据值和与之关联的数据类型的命名实体，例如参数、变量或线网。

## 6.3 值集
### 6.3.1 逻辑值
SystemVerilog 值集包括以下四个基本值：
 - `0`——表示逻辑零或假条件
 - `1`——表示逻辑一或真条件
 - `x`——表示未知逻辑值
 - `z`——表示高阻态

`0` 和 `1` 是逻辑互补值。

当 `z` 值出现在门的输入处或在表达式中遇到时，通常的效果与 `x` 值相同。值得注意的例外是可以传递 `z` 值的金属氧化物半导体（MOS）原语。

这种原始数据类型的名称是 `logic`。此名称可用于声明对象和从 4 状态数据类型构造其他数据类型。SystemVerilog 的几种数据类型是 4 状态类型，可以存储所有四个逻辑值。4 状态向量的所有位都可以独立设置为四个基本值之一。有些 SystemVerilog 数据类型是 2 状态的，每个向量的位中只存储 0 或 1 值。其他例外是事件类型（见 6.17），它没有存储，以及实数类型（见 6.12）。

### 6.3.2 强度
语言除了线网的基本值信息还包括 *强度* 信息。这在第 28 章中详细描述。与线网的位相关联的附加强度信息不被视为数据类型的一部分。

在线网声明中可以指定两种类型的强度，如下所示：
 - 只有在声明 `trireg` 类型的线网时才应使用 *电荷强度*。
 - 只有在将连续赋值放置在声明该线网的语句中时才应使用 *驱动强度*。

门声明也可以指定驱动强度。有关门和强度的更多信息，请参见第 28 章。

#### 6.3.2.1 电荷强度
电荷强度规范仅应与 `trireg` 线网一起使用。`trireg` 线网应用于模拟电荷存储；电荷强度应指定由以下关键字之一指示的电容的相对大小：
 - `small`
 - `medium`
 - `large`

`trireg` 线网的默认电荷强度应为 `medium`。

`trireg` 线网可以模拟随时间衰减的电荷存储节点。电荷衰减的仿真时间应在 `trireg` 线网的延迟规范中指定（见 28.16.2）。

例如：
```verilog
    trireg a; // 电荷强度为中等的 `trireg` 线网
    trireg (large) #(0,0,50) cap1; // 电荷强度为大的 `trireg` 线网，电荷衰减时间为 50 个时间单位
    trireg (small) signed [3:0] cap2; // 电荷强度为小的 4 位有符号 `trireg` 向量
```

#### 6.3.2.2 驱动强度
驱动强度规范允许在声明该线网的语句中将连续赋值放置在线网上。有关线网驱动强度属性的详细信息，请参见第 28 章。

## 6.4 单一和聚合类型
数据类型分为 *单一* 和 *聚合* 两类。单一类型应为除未打包结构、未打包联合或未打包数组（见 7.4 数组）之外的任何数据类型。聚合类型应为未打包结构、未打包联合或未打包数组数据类型。单一变量或表达式表示单个值、符号或句柄。聚合表达式和变量表示一组单一值的集合。整数类型（见 6.11.1）始终为单一类型，即使它们可以切片为多个单一值。*字符串* 数据类型是单一类型，即使字符串可以类似于字节的未打包数组进行索引。

这些类别的定义是为了使运算符和函数可以简单地将这些数据类型作为一个集体组进行引用。例如，一些函数会递归地进入聚合变量，直到达到单一值，然后对每个单一值执行操作。

虽然类是一种类型，但没有直接的类类型变量或表达式，只有单一的类对象句柄。因此，类无需以这种方式分类（见第 8 章关于类的内容）。

## 6.5 线网和变量
数据对象分为两大组：变量和线网。这两组在赋值和保存值的方式上有所不同。

线网可以由一个或多个连续赋值、原语输出或通过模块端口进行赋值。多个驱动的结果值由线网类型的解析函数确定。线网不能被过程性地赋值。如果一个端口的一侧的线网由另一侧的变量驱动，那么就暗含了一个连续赋值。`force` 语句可以覆盖线网的值。释放后，线网返回到解析值。

变量可以由一个或多个过程性语句（包括过程性连续赋值）进行赋值。最后一次写入决定值。或者，变量可以由一个连续赋值或一个端口进行赋值。

变量可以是其他类型的打包或未打包聚合（见 7.4 打包和未打包类型）。对独立元素进行多次赋值是独立检查的。独立元素包括结构的不同成员或数组的不同元素。打包类型的每个位也是一个独立元素。因此，在打包类型的聚合中，聚合中的每个位都是一个独立元素。

左侧包含切片的赋值被视为对整个切片的单个赋值。因此，一个结构或数组可以有一个元素被过程性赋值，另一个元素被连续赋值。并且结构或数组的元素可以被多个连续赋值赋值，只要每个元素都不被多个连续赋值覆盖。

确切的规则是，对于变量的最长静态前缀的扩展中的任何项进行多次连续赋值或过程性和连续赋值的混合写入是错误的（见 11.5.3 关于最长静态前缀的定义）。

例如，假设以下结构声明：
```verilog
struct {
    bit [7:0] A;
    bit [7:0] B;
    byte C;
} abc;
```

以下语句是合法的对 `struct` `abc` 的赋值：
```verilog
assign abc.C = sel ? 8'hBE : 8'hEF;
not (abc.A[0],abc.B[0]),
    (abc.A[1],abc.B[1]),
    (abc.A[2],abc.B[2]),
    (abc.A[3],abc.B[3]);
always @(posedge clk) abc.B <= abc.B + 1;
```

以下额外的语句是对结构 `abc` 的非法赋值：
```verilog
// 对 abc.C 进行多次连续赋值
assign abc.C = sel ? 8'hDE : 8'hED;
// 混合连续和过程性赋值给 abc.A[3]
always @(posedge clk) abc.A[7:3] <= !abc.B[7:3];
```

对于上述规则，声明的变量初始化或过程性连续赋值被视为过程性赋值。`force` 语句覆盖过程性赋值，过程性赋值覆盖正常赋值。`force` 语句既不是连续赋值也不是过程性赋值。

当一个变量连接到输入端口声明时，将暗含一个连续赋值。这使得对一个声明为输入端口的变量的赋值非法。当一个变量连接到实例的输出端口时，将暗含一个连续赋值。这使得将一个连接到实例的输出端口的变量进行额外的过程性或连续赋值非法。

变量不能连接到 `inout` 端口的任一侧。变量可以通过 `ref` 端口类型在端口之间共享。有关端口和端口连接规则的更多信息，请参见 23.3.3。

如果连续赋值可能向变量驱动除 `St0`、`St1`、`StX` 或 `HiZ` 之外的强度，则编译器可以发出警告。在任何情况下，将应用自动类型转换到赋值，并丢失强度。

与线网不同，变量不能在其声明的一部分具有隐式连续赋值。声明变量的赋值是变量初始化，而不是连续赋值。

例如：
```verilog
wire w = vara & varb; // 具有连续赋值的线网
logic v = consta & constb; // 具有初始化的变量
logic vw; // 没有初始赋值
assign vw = vara & varb; // 对变量的连续赋值
real circ;
assign circ = 2.0 * PI * R; // 对变量的连续赋值
```

数据在使用之前必须声明，除了隐式线网（见 6.10）。

在一个命名空间（见 3.13）中，不得重新声明已由线网、变量或其他声明声明的名称。

## 6.6 线网类型
有两种不同类型的线网：内置和用户定义。*线网* 类型可以表示结构实体之间的物理连接，例如门。线网的值不应存储（除非是 `trireg` 线网）。相反，它的值应由其驱动器的值确定，例如连续赋值或门。这些构造的定义见第 10 章和第 28 章。如果没有驱动器连接到线网，则其值应为高阻态（`z`），除非线网是 `trireg`，在这种情况下，它应保持先前驱动的值。

内置线网类型有几种不同类型，如表 6-1 所示。

表 6-1—内置线网类型
| wire | tri | tri0 | supply0 |
| ---- | --- | ---- | ------- |
| wand | triand | tri1 | supply1 |
| wor | trior | trireg | uwire |

### 6.6.1 wire 和 tri 网
*wire* 和 *tri* 网连接元素。网类型 `wire` 和 `tri` 在语法和功能上应相同；提供两个名称，以便网的名称可以指示该模型中网的目的。`wire` 网可用于由单个门或连续赋值驱动的网。`tri` 网类型可用于多个驱动器驱动网的情况。

在线网或 tri 网上的多个来源的逻辑冲突导致 x（未知）值。

表 6-2 是解决 `wire` 和 `tri` 网上多个驱动器的真值表。它假定两个驱动器的强度相等。有关逻辑强度建模的讨论，请参见 28.11。

表 6-2——wire 和 tri 网的真值表
| wire/tri | 0 | 1 | x | z |
| ------- | - | - | - | - |
| 0 | 0 | x | x | 0 |
| 1 | x | 1 | 1 | x |
| x | x | x | x | x |
| z | 0 | 1 | x | z |

### 6.6.2 无法解析的网
*uwire* 网是无法解析或单驱动器线网，用于模拟只允许单个驱动器的网。`uwire` 类型可用于强制执行此限制。将 uwire 网的任何位连接到多个驱动器将是一个错误。将 uwire 网连接到双向传递开关的双向端口将是一个错误。

在 23.3.3.6 中的端口连接规则在整个网层次结构中强制执行此限制，否则将发出警告。

### 6.6.3 有线网
*wired* 网是 `wor`、`wand`、`trior` 和 `triand` 类型，用于模拟有线逻辑配置。wired 网使用不同的真值表来解决多个驱动器驱动同一网时产生的冲突。`wor` 和 `trior` 网应创建 *有线* 或配置，以便当任何驱动器为 1 时，网的结果值为 1。`wand` 和 `triand` 网应创建有线和配置，以便如果任何驱动器为 0，则网的值为 0。

线网类型 `wor` 和 `trior` 在语法和功能上应相同。线网类型 `wand` 和 `triand` 在语法和功能上应相同。表 6-3 和表 6-4 给出了有线网的真值表，假设两个驱动器的强度相等。有关逻辑强度建模的讨论，请参见 28.11。

表 6-3——wand 和 triand 网的真值表
| wand/triand | 0 | 1 | x | z |
| ----------- | - | - | - | - |
| 0 | 0 | 0 | 0 | 0 |
| 1 | 0 | 1 | x | 1 |
| x | 0 | x | x | x |
| z | 0 | 1 | x | z |

表 6-4——wor 和 trior 网的真值表
| wor/trior | 0 | 1 | x | z |
| --------- | - | - | - | - |
| 0 | 0 | 1 | x | 0 |
| 1 | 1 | 1 | 1 | 1 |
| x | x | 1 | x | x |
| z | 0 | 1 | x | z |

### 6.6.4 Trireg 网
*trireg* 网存储一个值，用于模拟电荷存储节点。trireg 网可以处于两种状态之一，如下所示：
 - *驱动状态*：当 `trireg` 网的至少一个驱动器的值为 1、0 或 x 时，解析值传播到 `trireg` 网中，并且是 `trireg` 网的驱动值。
 - *电容状态*：当 `trireg` 网的所有驱动器都处于高阻态值（z）时，`trireg` 网保留其上次驱动的值；高阻态值不会从驱动器传播到 `trireg`。

`trireg` 网在电容状态下的值强度可以是 `small`、`medium` 或 `large`，具体取决于在 `trireg` 网的声明中指定的大小。`trireg` 网在驱动状态下的值强度可以是 `supply`、`strong`、`pull`、或 `weak`，具体取决于驱动器的强度。

例如，图 6-1 显示了包括 `medium`大小的 `trireg` 网、其驱动器和仿真结果的原理图。

![alt text](trireg.png)
图 6-1——trireg 和它的驱动的仿真值

 - a) 在仿真时间 0，线网 a 和线网 b 的值为 1。具有 `strong` 强度的值 1 从与门通过连接到线网 c 的 nmos 开关传播到 `trireg` 网 d。
 - b) 在仿真时间 10，线网 a 的值更改为 0，将线网 c 从与门断开。当线网 c 不再连接到与门时，线网 c 的值更改为高阻态。线网 b 的值保持为 1，因此线网 c 通过 nmos2 开关仍然连接到 `trireg` 网 d。高阻态值不会从线网 c 传播到 `trireg` 网 d。相反，`trireg` 网 d 进入电容状态，存储其上次驱动的值 1。它以 `medium` 强度存储 1。

#### 6.6.4.1 电容网络
电容网络是两个或多个 `trireg` 网之间的连接。在电容网络中，处于电容状态的 `trireg` 网之间可以传播逻辑和强度值。

例如，图 6-2 显示了一个电容网络，其中 `trireg` 网处于电容状态，其逻辑值更改了其他 `trireg` 网的逻辑值。
![alt text](capacitive_network.png)
图 6-2——电容网络的仿真结果

在图 6-2 中，`trireg_la` 网的电容强度为 `large`，`trireg_me1` 和 `trireg_me2` 网的电容强度为 `medium`，`trireg_sm` 网的电容强度为 `small`。仿真报告以下事件序列：
 - a) 在仿真时间 0，线网 a 和线网 b 的值为 1。线网 c 驱动值 1 到 `trireg_la` 和 `trireg_sm`；线网 d 驱动值 1 到 `trireg_me1` 和 `trireg_me2`。
 - b) 在仿真时间 10，线网 b 的值更改为 0，将 `trireg_sm` 和 `trireg_me2` 从其驱动器断开。这些 `trireg` 网进入电容状态，并存储其上次驱动的值 1。
 - c) 在仿真时间 20，线网 c 驱动值 0 到 `trireg_la`。
 - d) 在仿真时间 30，线网 d 驱动值 0 到 `trireg_me1`。
 - e) 在仿真时间 40，线网 a 的值更改为 0，将 `trireg_la` 和 `trireg_me1` 从其驱动器断开。这些 `trireg` 网进入电容状态，并存储值 0。
 - f) 在仿真时间 50，线网 b 的值更改为 1。
 - g) 线网 b 的值更改后，将 `trireg_sm` 连接到 `trireg_la`；这些 `trireg` 网的大小不同，存储了不同的值。这种连接导致较小的 `trireg` 网存储较大 `trireg` 网的值，因此 `trireg_sm` 现在存储值 0。

线网 b 的值更改还将 `trireg_me1` 连接到 `trireg_me2`；这些 `trireg` 网的大小相同，存储了不同的值。连接导致 `trireg_me1` 和 `trireg_me2` 都更改为 x。

在电容网络中，电荷强度从较大的 `trireg` 网传播到较小的 `trireg` 网。图 6-3 显示了一个电容网络及其仿真结果。
![alt text](charge_share.png)
图 6-3——电荷共享的仿真结果

在图 6-3 中，`trireg_la` 的电容强度是大，`trireg_sm` 的电容强度是小。仿真报告以下结果：
 - a) 在仿真时间 0，线网 a、线网 b 和线网 c 的值为 1。线网 a 驱动强值 1 到 `trireg_la` 和 `trireg_sm`。
 - b) 在仿真时间 10，线网 b 的值更改为 0，将 `trireg_la` 和 `trireg_sm` 从线网 a 断开。`trireg_la` 和 `trireg_sm` 进入电容状态。这两个 `trireg` 网通过 tranif1_2 保持连接，因此它们共享 `trireg_la` 的大电荷。
 - c) 在仿真时间 20，线网 c 的值更改为 0，将 `trireg_sm` 从 `trireg_la` 断开。`trireg_sm` 不再共享 `trireg_la` 的大电荷，现在存储小电荷。
 - d) 在仿真时间 30，线网 c 的值更改为 1，连接两个 `trireg` 网。这些 `trireg` 网现在共享相同的电荷。
 - e) 在仿真时间 40，线网 c 的值再次更改为 0，将 `trireg_sm` 从 `trireg_la` 断开。`trireg_sm` 不再共享 `trireg_la` 的大电荷，现在存储小电荷。

#### 6.6.4.2 理想电容状态和电荷衰减
`trireg` 网可以永久保留其值，或者其电荷可以随时间衰减。电荷衰减的仿真时间在 `trireg` 网的延迟规范中指定。有关电荷衰减的解释，请参见 28.16.2。

### 6.6.5 Tri0 和 tri1 网
`tri0` 和 `tri1` 网建模在其上有电阻 *下拉* 和电阻 *上拉* 器件的网。`tri0` 网等效于一个由连续 0 值的 `pull` 驱动的线网。`tri1` 网等效于一个由连续 1 值的 `pull` 驱动的线网。

当没有驱动器驱动 `tri0` 网时，其值为 0，强度为 `pull` 。当没有驱动器驱动 `tri1` 网时，其值为 1，强度为 `pull` 。当 `tri0` 或 `tri1` 网上有驱动器时，驱动器与隐式驱动在网上驱动的 `pull` 值相结合，以确定网的值。有关逻辑强度建模的讨论，请参见 28.11。

表 6-5 和表 6-6 是建模 `tri0` 和 `tri1` 网上多个强度为 `strong` 的驱动器的真值表。除非两个驱动器都是 z，否则网上的结果值具有强度强，否则网上的结果值具有 `pull` 强度。

表 6-5——tri0 网的真值表
| tri0 | 0 | 1 | x | z |
| ---- | - | - | - | - |
| 0 | 0 | x | x | 0 |
| 1 | x | 1 | x | 1 |
| x | x | x | x | x |
| z | 0 | 1 | x | 0 |

表 6-6——tri1 网的真值表
| tri1 | 0 | 1 | x | z |
| ---- | - | - | - | - |
| 0 | 0 | x | x | 0 |
| 1 | x | 1 | x | 1 |
| x | x | x | x | x |
| z | 0 | 1 | x | 1 |

### 6.6.6 供应网
供应网 `supply0` 和 `supply1` 可用于建模电路中的电源。这些网应具有 `supply` 强度。

### 6.6.7 用户定义的网类型
用户定义的 `nettype` 允许用户描述线网中的更一般的抽象值，包括其解析函数。`nettype` 类似于某些方面的 `typedef`，但只能在声明网时使用。它为特定数据类型提供了一个名称，以及可选的关联解析函数。

网类型声明的语法如 Syntax 6-1 所示。
```verilog
net_type_declaration ::= // from A.2.1.3
nettype data_type net_type_identifier 
[ with [ package_scope | class_scope ] tf_identifier ] ;
| nettype [ package_scope | class_scope ] net_type_identifier net_type_identifier ;
```

语法 6-1—网类型声明的语法（摘自附录 A）

使用 `nettype` 声明的网使用该数据类型，如果指定，则使用关联的解析函数。用户定义的 `nettype` 需要一个显式的数据类型。

对于用户定义的 `nettype`，对网的数据类型有一些限制。网的数据类型应为以下数据类型之一：
 - 4 状态整数类型，包括打包数组、打包结构或联合。
 - 2 状态整数类型，包括具有 2 状态数据类型成员的打包数组、打包结构或联合。
 - 实数或 shortreal 类型。
 - 固定大小的未打包数组、未打包结构或联合，其中每个元素都是用户定义的网类型的有效数据类型。

`nettype` 声明的第二种形式是为现有网类型创建另一个名称。

原子网是其值作为整体更新和解析的网。使用用户定义的 `nettype` 声明的网是原子网。同样，逻辑网是原子网，但逻辑向量网不是原子网，因为每个逻辑元素都是独立解析和更新的。虽然原子网可以具有单一或聚合值，但每个原子网都旨在描述设计中的单个连接点。

用户定义的 `nettype` 的解析由 SystemVerilog 函数声明指定。如果指定了解析函数，则当网的驱动器的值更改时，在 Active（或 Reactive）区域的网上安排更新事件。当更新事件成熟时，模拟器调用与该网类型关联的解析函数来计算网的值，该值是从驱动器的值计算而来的。函数的返回类型应与 `nettype` 的数据类型匹配。函数应接受任意数量的驱动器，因为网的不同实例可能连接到不同数量的驱动器。驱动器的值的任何更改都应触发与该网类型关联的解析函数的评估。

`nettype` 的解析函数应为自动的（或不保留状态信息）并且没有副作用。解析函数不应调整动态数组输入参数的大小，也不应写入动态数组输入参数的任何部分。虽然类函数方法可以用作解析函数，但这种函数应该是类静态方法，因为方法调用发生在没有类对象参与的调用上下文中。这种方法的参数化变体可以通过使用参数化类方法来创建，如 13.8 中所述。

两种不同的网类型可以使用相同的数据类型，但具有不同的解析函数。可以声明没有解析函数的 `nettype`，在这种情况下，对于具有该 `nettype` 的网具有多个驱动器是错误的。

由于调度区域内的不确定性，如果在调度区域内有多个驱动器更新，则可能会多次评估解析函数。

`force` 语句可以覆盖用户定义 `nettype` 的网的值。释放后，网返回到解析值。

```verilog
// 用户定义的数据类型 T
typedef struct {
    real field1;
    bit field2;
} T;

// 用户定义的解析函数 Tsum
function automatic T Tsum (input T driver[]);
    Tsum.field1 = 0.0;
    foreach (driver[i])
        Tsum.field1 += driver[i].field1;
    endfunction

nettype T wT; // 一个未解析的数据类型为 T 的 wT 网
// 一个数据类型为 T 的 wTsum 网，解析函数为 Tsum
nettype T wTsum with Tsum;

// 用户定义的数据类型 TR
typedef real TR[5];
// 一个未解析的数据类型为实数数组的 wTR 网
nettype TR wTR;

// 为 nettype wTsum 声明另一个名称 nettypeid2
nettype wTsum nettypeid2;
```

以下示例显示了如何使用参数化类定义与类静态方法来参数化用户定义 `nettype` 的数据类型。

```verilog
class Base #(parameter p = 1);
    typedef struct {
        real r;
        bit[p-1:0] data;
    } T;
    static function T Tsum (input T driver[]);
        Tsum.r = 0.0;
        Tsum.data = 0;
        foreach (driver[i])
            Tsum.data += driver[i].data;
        Tsum.r = $itor(Tsum.data);
    endfunction
endclass

typedef Base#(32) MyBaseT;
nettype MyBaseT::T narrowTsum with MyBaseT::Tsum;

typedef Base#(64) MyBaseType;
nettype MyBaseType::T wideTsum with MyBaseType::Tsum;

narrowTsum net1; // 数据宽度为 32 位
wideTsum net2; // 数据宽度为 64 位
```

### 6.6.8 通用互连
在 SystemVerilog 中，可以使用网类型和配置来创建具有不同抽象级别的设计模型。为了支持主要指定设计元素实例和设计元素之间的网连接的网表设计，SystemVerilog 定义了一种通用形式的网。这种通用网允许将网连接的规范与连接的类型分离。

声明为 `interconnect`（互连网或端口）的网或端口表示无类型或通用网。这种网或端口仅能表达网端口和终端连接，并且不得在任何过程性上下文或任何连续或过程性连续赋值中使用。`interconnect` 网或端口不得在除了所有网或端口都是 `interconnect` 的 net_lvalue 表达式之外的任何表达式中使用。即使数组中的不同位被解析为不同的网类型，也应将 `interconnect` 数组视为有效，如下面的示例所示。可以在 `interconnect` net_lvalue 中指定 net_alias 语句。有关 `interconnect` 网的端口和终端连接规则，请参见 23.3.3.7.1 和 23.3.3.7.2。

```verilog
package NetsPkg;
    nettype real realNet;
endpackage : NetsPkg

module top();
    interconnect [0:1] iBus;
    lDriver l1(iBus[0]);
    rDriver r1(iBus[1]);
    rlMod m1(iBus);
endmodule : top

module lDriver(output wire logic out);
endmodule : lDriver

module rDriver
    import NetsPkg::*;
    (output realNet out);
endmodule : rDriver

module rlMod(input interconnect [0:1] iBus);
    lMod l1(iBus[0]);
    rMod r1(iBus[1]);
endmodule : rlMod
```

以下简单示例用于说明 `interconnect` 网的有用性。该示例包含一个顶层模块（top），该模块实例化一个激励模块（driver）和一个比较器模块（cmp）。此配置旨在比较两个元素并确定它们是否相等。根据两个不同版本的配置，由两个不同的 `config` 块描述：一个用于 `real` 值，一个用于 `logic` 值。通过使用无类型的 `interconnect` 网，我们可以在不必更改测试台本本身的情况下，使用相同的测试台本与两个配置。`interconnect` 网 aBus 从其连接的类型中获取数据类型。

```verilog
<file lib.map>
library realLib *.svr;
library logicLib *.sv;

config cfgReal;
    design logicLib.top; 
    default liblist realLib logicLib;
endconfig

config cfgLogic; 
    design logicLib.top; 
    default liblist logicLib realLib;
endconfig

<file top.sv>
module top();
    interconnect [0:3] [0:1] aBus;
    logic [0:3] dBus;
    driver driverArray[0:3](aBus);
    cmp cmpArray[0:3](aBus,rst,dBus);
endmodule : top

<file nets.pkg>
package NetsPkg;
    nettype real realNet;
endpackage : NetsPkg

<file driver.svr>
module driver
    import NetsPkg::*; 
    #(parameter int delay = 30,
                int iterations = 256)
    (output realNet [0:1] out);
    timeunit 1ns / 1ps;
    real outR[1:0];
    assign out = outR;
    initial begin
        outR[0] = 0.0;
        outR[1] = 3.3;
        for (int i = 0; i < iterations; i++) begin
            #delay outR[0] += 0.2;
            outR[1] -= 0.2;
        end
    end
endmodule : driver

<file driver.sv>
module driver #(parameter int delay = 30,
                          int iterations = 256)
               (output wire logic [0:1] out);
    timeunit 1ns / 1ps;
    logic [0:1] outvar;

    assign out = outvar;
    
    initial begin
        outvar = '0;
        for (int i = 0; i < iterations; i++)
            #delay outvar++;
    end
endmodule : driver

<file cmp.svr>
module cmp
    import NetsPkg::*; 
    #(parameter real hyst = 0.65)
     (input realNet [0:1] inA,
     input logic rst,
     output logic out);
    timeunit 1ns / 1ps;
    real updatePeriod = 100.0;

    initial out = 1’b0;

    always #updatePeriod begin
        if (rst) out <= 1’b0;
        else if (inA[0] > inA[1]) out <= 1’b1;
        else if (inA[0] < inA[1] - hyst) out <= 1’b0;
    end
endmodule : cmp
<file cmp.sv>
module cmp #(parameter real hyst = 0.65)
            (input wire logic [0:1] inA,
    input logic rst,
    output logic out);

    initial out = 1’b0;

    always @(inA, rst) begin
        if (rst) out <= 1'b0;
        else if (inA[0] & ~inA[1]) out <= 1'b1;
        else out <= 1'b0;
    end
endmodule : cmp
```

## 6.7 线网声明
线网声明的语法如 Syntax 6-2 所示。

---
```verilog
net_declaration12 ::= // from A.2.1.3
net_type [ drive_strength | charge_strength ] [ vectored | scalared ] 
data_type_or_implicit [ delay3 ] list_of_net_decl_assignments ;
| net_type_identifier [ delay_control ] 
list_of_net_decl_assignments ;
| interconnect implicit_data_type [ # delay_value ] 
net_identifier { unpacked_dimension } 
[ , net_identifier { unpacked_dimension }] ;
net_type ::= // from A.2.2.1
supply0 | supply1 | tri | triand | trior | trireg | tri0 | tri1 | uwire | wire | wand | wor
drive_strength ::= // from A.2.2.2
( strength0 , strength1 )
| ( strength1 , strength0 )
| ( strength0 , highz1 )
| ( strength1 , highz0 )
| ( highz0 , strength1 )
| ( highz1 , strength0 )
strength0 ::= supply0 | strong0 | pull0 | weak0
strength1 ::= supply1 | strong1 | pull1 | weak1
charge_strength ::= ( small ) | ( medium ) | ( large )
delay3 ::= // from A.2.2.3
# delay_value | # ( mintypmax_expression [ , mintypmax_expression [ , mintypmax_expression ] ] )
delay2 ::= # delay_value | # ( mintypmax_expression [ , mintypmax_expression ] )
delay_value ::= 
unsigned_number 
| real_number 
| ps_identifier 
| time_literal 
| 1step
list_of_net_decl_assignments ::= net_decl_assignment { , net_decl_assignment } // from A.2.3
net_decl_assignment ::= net_identifier { unpacked_dimension } [ = expression ] // from A.2.4
---
```
语法 6-2—网声明的语法（摘自附录 A）

### 6.7.1 具有内置网类型的线网声明
没有赋值且其 `nettype` 不是用户定义 `nettype` 的网声明在本节中描述。具有赋值的线网声明在第 10 章中描述。

线网声明以确定线网值如何解析的线网类型开始。声明可以包括可选信息，如延迟值、驱动或电荷强度和数据类型。

如果一组线网共享相同的特性，则可以在同一声明语句中声明它们。

任何 4 状态数据类型都可以用于声明线网。例如：
```verilog
trireg (large) logic #(0,0,0) cap1;
typedef logic [31:0] addressT;
wire addressT w1;
wire struct packed { logic ecc; logic [7:0] data; } memsig;
```

如果在线网声明中未指定数据类型，或者仅指定了范围和/或签名，则网的数据类型将隐式声明为 `logic`。例如：
```verilog
wire w; // 等效于 "wire logic w;"
wire [15:0] ww; // 等效于 "wire logic [15:0] ww;"
```

作为 `interconnect` 声明的网应：
 - 没有数据类型，但可以有可选的打包或未打包维度；
 - 不指定驱动强度或电荷强度；
 - 不具有赋值表达式；
 - 指定最多一个延迟值。

对网的数据类型有一些限制。网的有效数据类型应为以下数据类型之一：
    - 4 状态整数类型，包括打包数组或打包结构。
    - 固定大小的未打包数组或未打包结构，其中每个元素都是网的有效数据类型。

这种递归定义的效果是，网完全由 4 状态位组成，并相应地处理。除了信号值之外，网的每个位应具有额外的强度信息。当信号位组合时，将根据 28.12 中描述的方式确定结果信号的强度和值。

在网或端口声明中使用 `reg` 关键字的词法限制。线网类型关键字后面不应直接跟随 `reg` 关键字。因此，以下声明是错误的：
```verilog
tri reg r;
inout wire reg p;
```

如果在网类型关键字和 `reg` 关键字之间有词法元素，则可以在网或端口声明中使用 `reg` 关键字。

线网的默认初始化值应为 z 值。具有驱动器的网应假定其驱动器的输出值。`trireg` 网是一个例外。`trireg` 网的默认值应为 x 值，其强度在网声明中指定（`small`、`medium` 或 `large`）。

如 6.6.8 中所述，`interconnect` 在其声明和使用方面受到限制。以下是一些合法和非法的 `interconnect` 声明示例：
```verilog
interconnect w1; // 合法
interconnect [3:0] w2; // 合法
interconnect [3:0] w3 [1:0]; // 合法
interconnect logic [3:0] w4; // 非法 – 指定了数据类型
interconnect #(1,2,3) w5; // 非法 – 仅允许一个延迟
assign w1 = 1; // 非法 – 不允许在连续赋值中
initial $display(w1); // 非法 – 不允许在过程上下文中
```

### 6.7.2 具有用户定义网类型的网声明
用户定义的网类型允许用户描述线网中的更一般的抽象值。网类型声明使用数据类型和该网类型的任何关联解析函数。

```verilog
// 未解析的网类型 wT，其数据类型为 T
// 有关数据类型 T 的声明，请参见 6.6.7 中的示例
nettype T wT;

// 一个数据类型为 T 和解析函数为 Tsum 的 wTsum 网类型
// 有关 Tsum 的声明，请参见 6.6.7 中的示例
nettype T wTsum with Tsum;

// 一个未解析的 wT 网
wT w1;

// 一个数组，每个网元素都是未解析的 wT 网类型
wT w2[8];

// 一个解析的 wTsum 网类型和解析函数为 Tsum
wTsum w3;

// 一个数组，每个网都是解析的 wTsum 网类型
wTsum w4[8];

// 用户定义的数据类型 TR，它是一个实数数组
typedef real TR[5];

// 一个未解析的 wTR 网类型，其数据类型为 TR
nettype TR wTR;

// 一个未解析的 wTR 网类型和数据类型 TR
wTR w5;

// 一个数组，每个网都有未解析的 wTR 网类型和数据类型 TR
wTR w6[8];
```

### 6.7.3 使用用户定义网类型初始化网
用户定义网类型的任何网的解析函数在时间零时至少一次被激活。即使在时间零时没有驱动器或驱动器上的值更改，也会发生此激活。这种激活即使对于没有驱动器或驱动器上的值更改的网也会发生。由于解析函数的实际评估受调度的不确定性影响，因此不能假设在保证调用之前或之后的时间零时的驱动器值的状态，这可能在时间零时之前或之后发生任何驱动器更改。

用户定义网类型的任何网的初始值应在启动任何初始或始终过程之前设置，并在激活保证时间零时解析调用之前设置。用户定义网类型的网的默认初始化值应为数据类型定义的默认值。表 6-7 定义了变量的数据类型的默认值，如果没有提供初始化程序；这些默认值也适用于用户定义网类型的网的有效数据类型。对于数据类型为结构类型的网，应用结构内成员的任何初始化表达式。

注意——用户定义网类型的逻辑网的默认值为 X。这个默认值意味着如果逻辑数据类型的位没有驱动器，则它的值将是 X，而不是 Z。对于具有解析网类型的网，如果没有驱动器，则值将由执行带有空驱动器值数组的解析函数确定。

## 6.8 变量声明
*变量* 是数据存储元素的抽象。变量应在一个赋值到下一个赋值之间存储一个值。在过程中的赋值语句充当触发器，改变数据存储元素中的值。

变量声明的语法如 Syntax 6-3 所示。

---
```verilog
data_declaration10 ::= // from A.2.1.3
[ const ] [ var ] [ lifetime ] data_type_or_implicit list_of_variable_decl_assignments ;
| type_declaration 
... 
data_type ::= // from A.2.2.1
integer_vector_type [ signing ] { packed_dimension } 
| integer_atom_type [ signing ] 
| non_integer_type 
| struct_union [ packed [ signing ] ] { struct_union_member { struct_union_member } }
{ packed_dimension }13 
| enum [ enum_base_type ] { enum_name_declaration { , enum_name_declaration } }
{ packed_dimension } 
| string
| chandle
| virtual [ interface ] interface_identifier [ parameter_value_assignment ] [ . modport_identifier ] 
| [ class_scope | package_scope ] type_identifier { packed_dimension } 
| class_type 
| event
| ps_covergroup_identifier 
| type_reference14
integer_type ::= integer_vector_type | integer_atom_type 
integer_atom_type ::= byte | shortint | int | longint | integer | time
integer_vector_type ::= bit | logic | reg
non_integer_type ::= shortreal | real | realtime
signing ::= signed | unsigned
simple_type ::= integer_type | non_integer_type | ps_type_identifier | ps_parameter_identifier 
data_type_or_void ::= data_type | void
IEEE Std 1800-2012
IEEE STANDARD FOR SYSTEMVERILOG—UNIFIED HARDWARE DESIGN, SPECIFICATION, AND 
VERIFICATION LANGUAGE
65
Copyright © 2013 IEEE. All rights reserved.
variable_decl_assignment ::= // from A.2.4
variable_identifier { variable_dimension } [ = expression ] 
| dynamic_array_variable_identifier unsized_dimension { variable_dimension } 
[ = dynamic_array_new ] 
| class_variable_identifier [ = class_new ] 
// 10) 在不在过程上下文中的 data_declaration 中，使用 automatic 关键字是非法的。在 data_declaration 中，除非使用 var 关键字，否则不得省略显式的 data_type。
// 13) 当 packed 维度与 struct 或 union 关键字一起使用时，也应使用 packed 关键字。
// 14) 在网声明中使用 type_reference 时，应在 net 类型关键字之前使用 net 类型关键字；在变量声明中使用 type_reference 时，应在 var 关键字之前使用 var 关键字。
```
---
语法 6-3—变量声明的语法（摘自附录 A）

变量声明的一种形式由数据类型后跟一个或多个实例组成。
```verilog
shortint s1, s2[0:9];
```

另一种形式的变量声明以关键字 `var` 开头。在这种情况下，数据类型是可选的。如果未指定数据类型，或者仅指定了范围和/或签名，则数据类型将隐式声明为 `logic`。
```verilog
var byte my_byte; // 等效于 "byte my_byte;"
var v; // 等效于 "var logic v;"
var [15:0] vw; // 等效于 "var logic [15:0] vw;"
var enum bit { clear, error } status;
input var logic data_in;
var reg r;
```

如果一组变量共享相同的特性，则可以在同一声明语句中声明它们。

变量可以在声明中使用初始化程序，例如：
```verilog
int i = 0;
```

将静态变量的初始值设置为变量声明的一部分（包括静态类成员）应在启动任何 initial 或 always 过程之前发生（也请参见 6.21 和 10.5 关于具有静态和自动生命周期的变量初始化）。

注意——在 IEEE Std 1364-2005 中，作为声明的一部分指定的初始化值被执行，就好像在模拟开始后从初始过程中进行了赋值。

初始值不限于简单常量；它们可以包括运行时表达式，包括动态内存分配。例如，可以通过调用其 new 方法（请参见 15.4.1）创建并初始化静态类句柄或邮箱，或者通过调用 `$urandom` 系统任务将静态变量初始化为随机值。这可能需要在运行时进行特殊的预初始化传递。

表 6-7 包含了如果未指定初始化程序的变量的默认值。

表 6-7——变量的默认值
| 类型 | 默认值 |
| ---- | ------ |
| 4-state 整数 | x |
| 2-state 整数 | 0 |
| 实数 | 0.0 |
| 枚举 | 默认枚举值 |
| 字符串 | 空字符串 |
| 事件 | 新事件 |
| 类 | null |
| chandle | null |

线网和变量可以赋值为负数值，但只有有符号类型保留符号的重要性。byte、shortint、int、integer 和 longint 类型默认为有符号类型。其他网和变量类型可以显式声明为有符号类型。有关有符号和无符号网和变量如何由某些运算符处理的描述，请参见 11.4.3.1

## 6.9 向量声明
未指定范围的声明的数据对象被视为 1 位宽，并称为*标量*。使用范围声明的多位数据对象被视为*向量*。向量是标量的打包数组。

### 6.9.1 指定向量
范围说明符（[msb_constant_expression : lsb_constant_expression]）给多位 `reg`、`logic` 或 `bit` 向量中的各个位提供地址。由 *msb* 常量表达式指定的最高有效位是范围中的左值，由 *lsb* 常量表达式指定的最低有效位是范围中的右值。

msb 和 lsb 常量表达式（请参见 11.2.1）可以是任何整数值，包括正数、负数或零。它们不得包含任何未知（x）或高阻态位。lsb 值可以大于、等于或小于 msb 值。

向量应遵守模 2 的 n 次方（2^n）的算术规则，其中 n 是向量中的位数。reg、logic 和 bit 类型的向量应被视为无符号量，除非声明为有符号量或连接到声明为有符号量的端口（请参见 23.3.3.1 和 23.3.3.8）。

示例：
```verilog
wand w; // 一个标量 "wand" 网
tri [15:0] busa; // 一个 16 位总线
trireg (small) storeit; // 一个强度为 small 的电荷存储节点
logic a; // 一个标量变量
logic[3:0] v; // 一个由 v[3]、v[2]、v[1] 和 v[0] 组成的 4 位向量
logic signed [3:0] signed_reg; // 一个范围为 -8 到 7 的 4 位向量
logic [-1:4] b; // 一个 6 位向量
wire w1, w2; // 声明两个网
logic [4:0] x, y, z; // 声明三个 5 位变量
```

实现可以对向量的最大长度设置限制，但该限制至少应为 65536（2^16）位。

实现不需要检测整数操作的溢出。

### 6.9.2 向量线网的可访问性
*vectored* 和 *scalared* 是可选的建议关键字，用于向量网声明。如果实现了这些关键字，则可能会限制对向量网的某些操作。如果使用了关键字 `vectored`，则可能不允许位选择、部分选择和强度规范，并且 PLI 可能会认为网未展开。如果使用了关键字 `scalared`，则应允许网的位选择和部分选择，并且 PLI 应该认为网已展开。

例如：
```verilog
tri1 scalared [63:0] bus64; // 一个将被展开的总线
tri vectored [31:0] data; // 一个可能会被展开的总线
```

## 6.10 隐式声明
语法 6.7 和 6.8 中显示的语法应用于显式声明。在以下情况下，将假定隐式声明一个标量网：
 - 如果一个标识符在端口表达式声明中使用，则将假定一个隐式的默认类型网，其向量宽度为端口表达式声明的向量宽度。有关端口表达式声明的讨论，请参见 23.2.2.1
 - 如果一个标识符在原语实例的终端列表中使用，或者在模块、接口、程序或静态检查器实例的端口连接列表中使用（但不在过程检查器实例中，请参见 17.3），并且该标识符在实例出现的范围内之前没有被声明，或者在实例出现的范围内之前没有被直接引用的范围中被声明（请参见 23.9），则将假定一个标量网。
 - 如果一个标识符出现在连续赋值语句的左侧，并且该标识符在连续赋值语句出现的范围内之前没有被声明，或者在连续赋值语句出现的范围内之前没有被直接引用的范围中被声明（请参见 23.9），则将假定一个标量网。连续赋值语句的讨论，请参见 10.3。

隐式网声明应属于线网引用出现的范围。例如，如果隐式网是由引用在生成块中声明的，则该网只在该生成块中隐式声明。从生成块外部或在同一模块中的另一个生成块中对网的后续引用要么是非法的，要么会创建另一个不同网的隐式声明（取决于引用是否符合上述标准）。有关生成块的信息，请参见第 27 章。

有关控制使用 `` `default_nettype `` 编译器指令隐式声明的网类型的类型的讨论，请参见 22.8。

## 6.11 整数数据类型
SystemVerilog 提供了几种整数数据类型，如表 6-8 所示。

表 6-8——整数数据类型
| 类型 | 描述 |
| ---- | ---- |
| shortint | 2 状态数据类型，16 位有符号整数 |
| int | 2 状态数据类型，32 位有符号整数 |
| longint | 2 状态数据类型，64 位有符号整数 |
| byte | 2 状态数据类型，8 位有符号整数或 ASCII 字符 |
| bit | 2 状态数据类型，用户定义的向量大小，无符号 |
| logic | 4 状态数据类型，用户定义的向量大小，无符号 |
| reg | 4 状态数据类型，用户定义的向量大小，无符号 |
| integer | 4 状态数据类型，32 位有符号整数 |
| time | 4 状态数据类型，64 位无符号整数 |

### 6.11.1 整数类型
术语 *整数* 在本标准中用于指代可以表示单个基本整数数据类型、打包数组、打包结构、打包联合、枚举变量或时间变量的数据类型。

术语 *简单位向量类型* 在本标准中用于指代可以直接表示一维打包位数组的数据类型。表 6-8 中列出的整数类型都是预定义宽度的简单位向量类型。打包结构类型（参见 7.2）和多维打包数组类型（参见 7.4）不是简单位向量类型，但是每个都等效于（参见 6.22.2）某个简单位向量类型，可以轻松地互相转换。

### 6.11.2 2 状态（二值）和 4 状态（四值）数据类型
可以具有未知和高阻态值的类型称为 *4 状态类型*。这些是 `logic`、`reg`、`integer` 和 `time`。其他类型没有未知值，称为 *2 状态类型*，例如 `bit` 和 `int`。

`int` 和 `integer` 之间的区别在于 `int` 是 2 状态类型，而 `integer` 是 4 状态类型。4 状态值具有附加位，用于编码 X 和 Z 状态。2 状态数据类型可以更快地仿真，占用更少的内存，并且在某些设计风格中更受欢迎。

关键字 `reg` 并不总是准确描述用户意图，因为它可能被认为暗示硬件寄存器。关键字 `logic` 是一个更具描述性的术语。`logic` 和 `reg` 表示相同的类型。

从较少位数自动转换为较多位数涉及零扩展（如果无符号）或符号扩展（如果有符号）。从较多位数自动转换为较少位数涉及最高有效位（MSB）的截断。当 4 状态值自动转换为 2 状态值时，任何未知或高阻态位都应转换为零。

### 6.11.3 有符号和无符号整数类型
整数类型使用整数算术，可以是有符号或无符号的。这会影响某些运算符的含义（请参见第 11 章中的运算符和表达式）。

`byte`、`shortint`、`int`、`integer` 和 `longint` 默认为有符号的。`time`、`bit`、`reg` 和 `logic` 默认为无符号的，数组也是如此。可以使用关键字 `signed` 和 `unsigned` 明确定义有符号性。

```verilog
int unsigned ui;
int signed si;
```

## 6.12 real、shortreal 和 realtime 数据类型
`real` 数据类型是 C 语言中的 `double`。`shortreal` 数据类型是 C 语言中的 `float`。`realtime` 声明应与 `real` 声明视为同义，并且可以互换使用。这三种类型的变量统称为 *实数变量*。

### 6.12.1 运算符和实数
在实数和实数变量上使用逻辑或关系运算符的结果是一个单比特标量值。并非所有运算符都可以用于涉及实数和实数变量的表达式（请参见 11.3.1）。实数常量和实数变量在以下情况下也是禁止的：
 - 应用于实数变量的边沿事件控制（posedge、negedge、edge）
 - 实数声明中的位选择或部分选择引用的变量
 - 向量的位选择或部分选择引用的实数索引表达式

### 6.12.2 转换
实数应通过将实数四舍五入到最近的整数来转换为整数，而不是将其截断。当将实数分配给整数时，将发生隐式转换。如果实数的小数部分恰好为 0.5，则应将其远离零四舍五入。

当将表达式分配给实数时，应进行隐式转换。在转换时，网络或变量中的单个位如果为 x 或 z，则在转换时应视为零。

可以使用强制转换（请参见 6.24）或使用系统任务（请参见 20.5）来指定显式转换。

## 6.13 void 数据类型

*void* 数据类型表示不存在的数据。此类型可用于指示函数没有返回值。此类型还可用于标记联合的成员（请参见 7.3.2）。

## 6.14 Chandle 数据类型
*chandle* 数据类型表示使用 DPI（参见第 35 章）传递的指针的存储。该数据类型的值的大小取决于平台，但至少应足够大，以便在运行工具的机器上保存指针。

声明句法如下：
```verilog
chandle variable_name;
```

其中 *variable_name* 是有效的标识符。Chandles 应始终初始化为值 *null*，其在 C 侧的值为 0。Chandles 的使用受到限制，其唯一合法用途如下：
 - 仅在 `chandle` 变量上有效的操作符如下：
   - 与另一个 `chandle` 或 `null` 的相等性（`==`）、不等性（`!=`）
   - 与另一个 `chandle` 或 `null` 的情况相等性（`===`）、不等性（`!==`）（与 `==` 和 `!=` 的语义相同）
 - 可以测试 `chandle` 的布尔值，如果 chandle 为 `null`，则布尔值为 0，否则为 1。
 - 只能对 `chandle` 进行以下赋值：
   - 从另一个 `chandle` 赋值
   - 赋值为 `null`
 - 可以将 chandle 插入到关联数组中（参见 7.8），但是这种关联数组中任何两个条目的相对顺序可能会有所不同，即使是在同一工具的连续运行之间也可能如此。
 - 可以在类中使用 chandle。
 - 可以将 chandle 作为参数传递给子进程。
 - 可以从函数返回 chandle。

Chandles 的使用受到以下限制：
 - 端口不得具有 `chandle` 数据类型。
 - 不得将 chandle 赋值给任何其他类型的变量。
 - 不得如下使用 chandle：
   - 在除本子句允许的情况外的任何表达式中
   - 作为端口
   - 在敏感性列表或事件表达式中
   - 在连续赋值中
   - 在未标记的联合中
   - 在打包类型中

## 6.15 类
类变量可以保存对类对象的句柄。定义类和创建对象在第 8 章中讨论。

## 6.16 字符串数据类型
`string` 数据类型是字符的有序集合。`string` 变量的长度是集合中的字符数。`string` 类型的变量是动态的，因为它们的长度在仿真期间可能会变化。可以通过索引变量来选择读取或写入 `string` 变量的单个字符。`string` 变量的单个字符是 `byte` 类型。

SystemVerilog 还包括一些特殊方法来处理字符串，这些方法在本节中定义。

字符串变量不像字符串字面量（请参见 5.9）那样表示字符串。字符串字面量的行为类似于宽度为 8 位的多位数组。将字符串字面量分配给不同大小的整数变量时，字符串字面量将被截断为变量的大小，或者根据需要在左侧填充零。使用 `string` 数据类型而不是整数变量时，字符串可以是任意长度，不会发生截断。将字符串字面量分配给 `string` 类型或使用 `string` 类型操作数的表达式时，字符串字面量将隐式转换为 `string` 类型。

字符串变量的索引应从 0 到 N-1（其中 N 是字符串的长度），以便索引变量。字符串变量可以采用特殊值 `""`（空字符串），索引空字符串变量将是越界访问。

字符串变量不得包含特殊字符“\0”。将值 0 分配给字符串字符将被忽略。

声明字符串变量的语法如下：
```verilog
string variable_name [= initial_value];
```

其中 *variable_name* 是有效的标识符，可选的 *initial_value* 可以是字符串字面量、空字符串的值或字符串数据类型表达式。例如：
```verilog
parameter string default_name = "John Smith";
string myName = default_name;
```

如果在声明中未指定初始值，则变量将初始化为 `""`（空字符串）。空字符串的长度为零。

SystemVerilog 提供了一组运算符，可用于操作字符串变量和字符串字面量的组合。在表 6-9 中列出了 `string` 数据类型的基本运算符。

字符串字面量可以分配给 `string` 类型或整数数据类型的变量。将字符串字面量分配给整数数据类型的变量时，如果数据对象的位数不等于字符串字面量中的字符数乘以 8，则字符串字面量将右对齐，并根据需要在左侧截断或填充零。例如：
```verilog
byte c = "A"; // 将 "A" 分配给 c
bit [10:0] b = "\x41"; // 将 'b000_0100_0001' 分配给 b
bit [1:4][7:0] h = "hello"; // 将 "ello" 分配给 h
```

可以将字符串字面量或 `string` 类型表达式直接分配给 `string` 类型变量（*字符串变量*）。整数类型的值可以分配给字符串变量，但需要进行转换。将整数值转换为字符串变量时，该变量将增长或缩小以容纳整数值。如果整数值的大小不是 8 位的倍数，则该值将在左侧填充零，以使其大小为 8 位的倍数。

将字符串字面量分配给字符串变量时，将按以下步骤进行转换：
 - 字符串字面量中的所有“\0”字符将被忽略（即，从字符串中删除）。
 - 如果第一步的结果是空字符串字面量，则将分配空字符串。
 - 否则，将分配字符串字面量中剩余的字符。

将整数值转换为字符串变量的强制转换如下所示：
    - 如果整数值的大小（以位为单位）不是 8 的倍数，则将整数值左扩展并填充零，直到其大小为 8 的倍数。然后，将扩展值视为字符串字面量，其中每 8 位表示一个字符。
    - 然后应用上述用于字符串字面量转换的步骤。

例如：
```verilog
string s0 = "String literal assign"; // 将 s0 设置为 "String literal assign"
string s1 = "hello\0world"; // 将 s1 设置为 "helloworld"
bit [11:0] b = 12'ha41;
string s2 = string'(b); // 将 s2 设置为 16'h0a41
```

作为第二个示例：
```verilog
typedef logic [15:0] r_t;
r_t r;
integer i = 1;
string b = "";
string a = {"Hi", b};

r = r_t'(a); // OK
b = string'(r); // OK
b = "Hi"; // OK
b = {5{"Hi"}}; // OK
a = {i{"Hi"}}; // OK（非常量复制）
r = {i{"Hi"}}; // 无效（非常量复制）
a = {i{b}}; // OK
a = {a,b}; // OK
a = {"Hi",b}; // OK
r = {"H",""}; // 产生 "H"
```

表 6-9——字符串运算符
| 运算符 | 语义 |
| ------ | ---- |
| Str1 == Str2 | *相等*。检查两个字符串操作数是否相等。如果它们相等，则结果为 1；否则为 0。两个操作数都可以是字符串类型的表达式，或者一个可以是字符串类型的表达式，另一个可以是字符串字面量，该字面量将隐式转换为字符串类型以进行比较。如果两个操作数都是字符串字面量，则该运算符与整数类型的相等运算符相同。 |
| Str1 != Str2 | *不等*。等于的逻辑否定 |
| Str1 <  Str2 <br> Str1 <= Str2 <br> Str1 >  Str2 <br> Str1 >= Str2 | *比较*。如果使用两个字符串 Str1 和 Str2 的字典序，对应的条件为真，关系操作符返回 1。比较使用字符串的比较方法。两个操作数都可以是字符串类型的表达式，或者一个可以是字符串类型的表达式，另一个可以是字符串字面量，该字面量将隐式转换为字符串类型以进行比较。如果两个操作数都是字符串字面量，则该运算符与整数类型的比较运算符相同。 |
| {Str1,Str2,...,Strn} | *连接*。每个操作数都可以是字符串字面量或字符串类型的表达式。如果所有操作数都是字符串字面量，则表达式应该像整数值的连接一样行为；如果这样的连接的结果在涉及字符串类型的另一个表达式中使用，则应该隐式转换为字符串类型。如果至少一个操作数是字符串类型的表达式，则在执行连接之前应将任何字符串字面量操作数转换为字符串类型，连接的结果应为字符串类型。 |
| {multiplier{Str}} | *复制*。Str 可以是字符串字面量或字符串类型的表达式。multiplier 应该是整数类型的表达式，不需要是常量表达式。如果 multiplier 是非常量的，或者 Str 是字符串类型的表达式，则结果是一个字符串，其中包含 N 个 Str 的连接副本，其中 N 由 multiplier 指定。如果 Str 是字面量，multiplier 是常量，则表达式的行为类似于数字复制（如果结果在涉及字符串类型的另一个表达式中使用，则应隐式转换为字符串类型）。 |
| Str[index] | *索引*。返回一个字节，即给定索引处的 ASCII 代码。索引范围从 0 到 N-1，其中 N 是字符串中的字符数。如果给定超出范围的索引，则返回 0。在语义上等同于 Str.getc(index)。 |
| Str.method(...) | 使用点（.）运算符在字符串上调用指定的方法。 |

SystemVerilog 还包括一些处理字符串的特殊方法，这些方法使用内置的方法表示法。这些方法在 6.16.1 到 6.16.15 中描述。

### 6.16.1 Len()
`function int len();`

 - `str.len()` 返回字符串的长度，即字符串中的字符数。
 - 如果 `str` 是 `""`，则 `str.len()` 返回 0。

### 6.16.2 Putc()
`function void putc(int i, byte c);`

 - `str.putc(i, c)` 用给定的整数值替换字符串中的第 i 个字符。
 - `putc` 不会更改字符串的大小：如果 i < 0 或 i >= str.len()，则字符串保持不变。
 - 如果 `putc` 的第二个参数为零，则字符串不受影响。

`putc` 方法赋值 `str.putc(j, x)` 在语义上等同于 `str[j] = x`。

### 6.16.3 Getc()
`function byte getc(int i);`

 - `str.getc(i)` 返回字符串中第 i 个字符的 ASCII 代码。
 - 如果 i < 0 或 i >= str.len()，则 `str.getc(i)` 返回 0。

`getc` 方法赋值 `x = str.getc(j)` 在语义上等同于 `x = str[j]`。

### 6.16.4 Toupper()
`function string toupper();`

 - `str.toupper()` 返回一个字符串，其中的字符转换为大写。
 - 字符串保持不变。

### 6.16.5 Tolower()
`function string tolower();`

 - `str.tolower()` 返回一个字符串，其中的字符转换为小写。
 - 字符串保持不变。

### 6.16.6 Compare()
`function int compare(string s);`

 - `str.compare(s)` 比较 `str` 和 `s`，与 ANSI C 的 `strcmp` 函数相同，关于词法顺序和返回值。

请参见表 6-9 中的关系字符串运算符。

### 6.16.7 Icompare()
`function int icompare(string s);`

 - `str.icompare(s)` 比较 `str` 和 `s`，与 ANSI C 的 `strcmp` 函数相同，关于词法顺序和返回值，但比较是不区分大小写的。

### 6.16.8 Substr()
`function string substr(int i, int j);`

 - `str.substr(i, j)` 返回一个新字符串，由 `str` 中位置 i 到 j 的字符组成。
 - 如果 i < 0、j < i 或 j >= str.len()，则 `substr()` 返回 `""`（空字符串）。

### 6.16.9 Atoi(), atohex(), atooct(), atobin()
`function integer atoi();`
`function integer atohex();`
`function integer atooct();`
`function integer atobin();`

 - `str.atoi()` 返回与 `str` 中的 ASCII 十进制表示相对应的整数。例如：
```verilog
str = "123";
int i = str.atoi(); // 将 123 赋给 i。
```
转换扫描所有前导数字和下划线字符（_），并在遇到任何其他字符或字符串结束时立即停止。如果没有遇到数字，则返回零。它不解析整数文字的完整语法（符号、大小、撇号、基数）。
 - `atohex` 将字符串解释为十六进制。
 - `atooct` 将字符串解释为八进制。
 - `atobin` 将字符串解释为二进制。

注意：这些 ASCII 转换函数返回 32 位整数值。可能会发生截断而没有警告。要转换大于 32 位的整数值，请参见 21.3.4 中的 `$sscanf`。

### 6.16.10 Atoreal()
`function real atoreal();`

 - `str.atoreal()` 返回与 `str` 中的 ASCII 十进制表示相对应的实数。

转换解析实数常量。扫描遇到任何不符合此语法的字符或字符串结束时立即停止。如果没有遇到数字，则返回零。

### 6.16.11 Itoa()
`function void itoa(integer i);`

 - `str.itoa(i)` 将 `i` 的 ASCII 十进制表示存储到 `str` 中（`atoi` 的反函数）。

### 6.16.12 Hextoa()
`function void hextoa(integer i);`

 - `str.hextoa(i)` 将 `i` 的 ASCII 十六进制表示存储到 `str` 中（`atohex` 的反函数）。

### 6.16.13 Octtoa()
`function void octtoa(integer i);`

 - `str.octtoa(i)` 将 `i` 的 ASCII 八进制表示存储到 `str` 中（`atooct` 的反函数）。

### 6.16.14 Bintoa()
`function void bintoa(integer i);`

 - `str.bintoa(i)` 将 `i` 的 ASCII 二进制表示存储到 `str` 中（`atobin` 的反函数）。

### 6.16.15 Realtoa()
`function void realtoa(real r);`

 - `str.realtoa(r)` 将 `r` 的 ASCII 实数表示存储到 `str` 中（`atoreal` 的反函数）。

## 6.17 事件数据类型
事件对象提供了一种强大而有效的方法来描述两个或多个并发活动进程之间的通信和同步。一个基本的例子是一个小型波形时钟发生器，通过周期性地发出显式事件来同步同步电路的控制，而电路则等待事件的发生。

`event` 数据类型提供了同步对象的句柄。由事件变量引用的对象可以被显式触发并等待。此外，事件变量具有持久触发状态，该状态在整个时间步长的持续时间内持续。可以使用 9.4.2 中描述的事件控制语法来识别其发生。

事件变量可以分配或与另一个事件变量进行比较，或分配特殊值 `null`。当分配另一个事件变量时，两个事件变量都引用同一个同步对象。当分配 `null` 时，同步对象与事件变量之间的关联被断开。

如果在事件变量的声明中未指定初始值，则变量将初始化为新的同步对象。

示例：
```verilog
event done; // 声明一个名为 done 的新事件
event done_too = done; // 将 done_too 声明为 done 的别名
event empty = null; // 没有同步对象的事件变量
```

事件操作和语义在 15.5 中详细讨论。

## 6.18 用户定义类型
SystemVerilog 的数据类型可以使用 `typedef` 扩展为用户定义类型。声明用户定义类型的语法如下：

---
```verilog
type_declaration ::= // from A.2.1.3
typedef data_type type_identifier { variable_dimension } ;
| typedef interface_instance_identifier constant_bit_select . type_identifier type_identifier ;
| typedef [ enum | struct | union | class | interface class ] type_identifier ;
```
---

语法 6-4—用户定义类型（摘自附录 A）

`typedef` 可以用于为现有数据类型提供用户定义名称。例如：
```verilog
typedef int intP;
```

然后可以使用命名的数据类型，如下所示：
```verilog
intP a, b;
```

复杂数据类型转换（见 6.24）中必须使用用户定义的数据类型名称，只允许简单数据类型名称，并且在使用未打包数组类型时作为类型参数值（见 6.20.3）。

类型参数也可以用于声明 `type_identifier`。用户定义数据类型的声明必须在引用其 `type_identifier` 之前。用户定义数据类型标识符具有与数据标识符相同的作用域规则，但是不允许使用层次引用到 `type_identifier`。通过端口在接口中定义的类型标识符的引用不被视为层次引用，因此允许使用，前提是在使用之前在本地重新定义。这样的 `typedef` 称为 `基于接口的 typedef`。

```verilog
interface intf_i;
    typedef int data_t;
endinterface

module sub(intf_i p);
    typedef p.data_t my_data_t;
    my_data_t data;
    // 当连接到上面的接口时，'data'的类型将是int
endmodule
```

有时需要在定义类型的内容之前声明用户定义类型。这对于从基本数据类型派生的用户定义类型很有用：`enum`、`struct`、`union`、`interface class` 和 `class`。支持此功能的形式如下：
```verilog
typedef enum type_identifier;
typedef struct type_identifier;
typedef union type_identifier;
typedef class type_identifier;
typedef interface class type_identifier;
typedef type_identifier;
```

注意，空用户定义类型声明对于类的耦合定义很有用，如第 8.27 节所示，但不能用于结构的耦合定义，因为结构是静态声明的，而且没有结构的句柄支持。

最后一种形式显示了用户定义类型的基本数据类型不必在前向声明中定义。

前向 `typedef` 的实际数据类型定义应在同一本地作用域或生成块中解析。如果 `type_identifier` 未解析为数据类型，则会出错。如果前向类型声明指定了基本数据类型，并且实际类型定义不符合指定的基本数据类型，则会出错。在同一作用域中，前向类型声明可以在最终类型定义之前或之后。在同一作用域中，可以有多个相同类型标识符的前向类型声明。使用术语 `前向类型声明` 不要求前向类型声明在最终类型定义之前。在同一作用域中，可以有多个相同类型标识符的前向类型声明。

前向 `typedef` 应在最终类型定义之前解析。它是一个错误，如果前缀不解析为类，则使用类作用域解析运算符（参见 8.23）选择具有这样的前缀的类型。如果前缀不解析为类，则会出错。

```verilog
typedef C;
C::T x; // 非法；C 是一个不完整的前向类型
typedef C::T c_t; // 合法；通过 typedef 引用 C::T
c_t y;
class C;
typedef int T;
endclass
```

## 6.19 枚举
枚举类型必须使用语法6-5所示的语法来定义。

---
```verilog
data_type ::= // from A.2.2.1
... 
| enum [ enum_base_type ] { enum_name_declaration { , enum_name_declaration } }
{ packed_dimension } 
... 
enum_base_type ::= 
integer_atom_type [ signing ] 
| integer_vector_type [ signing ] [ packed_dimension ] 
| type_identifier [ packed_dimension ]
enum_name_declaration ::= 
enum_identifier [ [ integral_number [ : integral_number ] ] ] [ = constant_expression ] 
// 如果type_identifier表示integer_atom_type（不允许添加额外的打包维度）或integer_vector_type，那么它作为enum_base_type是合法的。
```
---

语法 6-5—枚举类型（摘自附录 A）

枚举类型声明了一组命名的整数常量。枚举数据类型提供了一种抽象声明强类型变量的方法，而不需要数据类型或数据值，并且稍后可以添加所需的数据类型和值，以便在需要更多定义的设计中使用。枚举数据类型还可以通过使用枚举名称而不是枚举值轻松引用或显示。

在没有数据类型声明的情况下，默认数据类型应为 `int`。在枚举类型中使用的任何其他数据类型都需要显式数据类型声明。

枚举类型定义了一组命名值。在下面的示例中，`light1` 和 `light2` 被定义为匿名（未命名）枚举 `int` 类型，其中包括三个成员：`red`、`yellow` 和 `green`。
```verilog
enum {red, yellow, green} light1, light2; // 匿名 int 类型
```

枚举名称与 x 或 z 赋值分配给没有显式数据类型或显式 2 状态声明的 `enum` 是一个语法错误。
```verilog
// 语法错误：IDLE=2'b00, XX=2'bx <ERROR>, S1=2'b01, S2=2'b10
enum bit [1:0] {IDLE, XX='x, S1=2'b01, S2=2'b10} state, next;
```

枚举类型的 4 状态类型声明，例如 `integer`，包括一个或多个具有 x 或 z 赋值的名称是允许的。
```verilog
// 正确：IDLE=0, XX='x, S1=1, S2=2
enum integer {IDLE, XX='x, S1='b01, S2='b10} state, next;
```

在枚举名称后面跟着一个具有 x 或 z 赋值的枚举名称是一个语法错误。
```verilog
// 语法错误：IDLE=0, XX='x, S1=??, S2=??
enum integer {IDLE, XX='x, S1, S2} state, next;
```

值可以转换为整数类型，并从 0 的初始值递增。这可以被覆盖。
```verilog
enum {bronze=3, silver, gold} medal; // silver=4, gold=5
```

可以为部分名称设置值，而不为其他名称设置值。`enum` 命名常量的可选值是一个建立时间常量表达式（见 6.20），可以包括对参数、本地参数、genvars、其他枚举命名常量和这些常量函数的引用。不允许使用层次名称和 `const` 变量。没有值的名称会自动分配前一个名称的增量值。自动增量到达枚举的最大可表示值将是一个错误。
```verilog
// c 自动分配 8 的增量值
enum {a=3, b=7, c} alphabet;
```

枚举类型中的枚举名称和它们的整数值必须是唯一的。无论是显式设置值还是自动增量，将两个值设置为相同的名称或将相同的值设置为两个名称都是错误的，无论这些值是显式设置的还是自动增量的。
```verilog
// 错误：c 和 d 都分配了 8
enum {a=0, b=7, c, d=8} alphabet;
```

如果第一个名称没有分配值，则它将被分配为 0 的初始值。
```verilog
// a=0, b=7, c=8
enum {a, b=7, c} alphabet;
```

整数值表达式在枚举基本类型的强制转换上下文中进行评估。如果枚举编码值超出枚举基本类型的可表示范围，则会出错。对于无符号基本类型，如果强制转换截断值并且任何被丢弃的位不为零，则会出错。对于有符号基本类型，如果强制转换截断值并且任何被丢弃的位不等于结果的符号位，则会出错。如果整数值表达式是一个大小化的文字常量，则如果大小与枚举基本类型不同，则会出错，即使值在可表示范围内。强制转换后的值是用于名称的值，包括在唯一性检查和自动增量以获得下一个名称的值中。
```verilog
// 正确声明 - bronze 和 gold 是无大小
enum bit [3:0] {bronze='h3, silver, gold='h5} medal2;

// 正确声明 - bronze 和 gold 的大小是多余的
enum bit [3:0] {bronze=4'h3, silver, gold=4'h5} medal3;

// bronze 和 gold 成员声明中的错误
enum bit [3:0] {bronze=5'h13, silver, gold=3'h5} medal4;

// c 声明错误，至少需要 2 位
enum bit [0:0] {a,b,c} alphabet;
```

在赋值、作为参数和与运算符一起使用的枚举类型的类型检查在 6.19.3 中讨论。与 C 一样，没有文字的重载；因此，medal2 和 medal3 不能在同一作用域中定义，因为它们包含相同的名称。

### 6.19.1 将新数据类型定义为枚举类型
可以给定类型名称，以便在许多地方使用相同的类型。
```verilog
typedef enum {NO, YES} boolean;
boolean myvar; // 命名类型
```

### 6.19.2 枚举类型范围
可以通过表 6-10 中显示的语法自动指定枚举元素的范围。

表 6-10—枚举元素范围
| name | 将下一个连续数字与名称关联 |
| ------------- | ---------------------------- |
| name = C | 将常量 C 与名称关联 |
| name[N] | 生成 N 个命名常量序列：name0、name1、...、nameN-1。N 必须是正整数。 |
| name[N] = C | 可以将常量分配给生成的命名常量，将该常量与第一个生成的命名常量关联；随后生成的命名常量关联连续值。N 必须是正整数。 |
| name[N:M] | 创建从 nameN 开始递增或递减直到达到nameM 的命名常量序列。N 和 M 必须是非负整数。 |
| name[N:M] = C | 可以将常量分配给生成的命名常量，将该常量与第一个生成的命名常量关联；随后生成的命名常量关联连续值。N 和 M 必须是非负整数。 |

例如：
```verilog
typedef enum { add=10, sub[5], jmp[6:8] } E1;
```

这个例子定义了枚举类型 E1，它将数字 10 分配给枚举命名常量 add。它还创建了枚举命名常量 sub0、sub1、sub2、sub3 和 sub4，并将它们分别分配值 11...15。最后，该示例创建了枚举命名常量 jmp6、jmp7 和 jmp8，并将它们分别分配值 16 到 18。

```verilog
enum { register[2] = 1, register[2:4] = 10 } vr;
```

### 6.19.3 类型检查
枚举类型是强类型的；因此，不能直接将枚举类型的变量分配给枚举集合之外的值，除非使用显式转换或除非枚举变量是联合的成员。这是一个强大的类型检查工具，可以防止用户意外地将不存在的值分配给枚举类型的变量。枚举值仍然可以用作常量表达式，并且结果可以分配给任何兼容的整数类型的变量。

枚举变量在赋值、参数和关系运算符中进行类型检查。枚举变量被自动转换为整数值，但是将任意表达式分配给枚举变量需要显式转换。

例如：
```verilog
typedef enum { red, green, blue, yellow, white, black } Colors;
```

这个操作为每个颜色标识符分配一个唯一的数字，并创建新的数据类型 Colors。这种类型可以用来创建该类型的变量。

```verilog
Colors c;
c = green;
c = 1; // 无效赋值
if ( 1 == c ) // OK。c 自动转换为整数
```

在前面的示例中，将值 green 分配给类型为 Colors 的变量 c。第二个赋值是无效的，因为枚举类型强制执行的严格类型规则。

可以使用转换来将不同数据类型或枚举类型的值分配给枚举类型。转换在 6.19.4、6.24.1 和 6.24.2 中讨论。

### 6.19.4 数值表达式中的枚举类型
枚举类型变量的元素可以用于数值表达式。在表达式中使用的值是与枚举值相关联的数值。例如：
```verilog
typedef enum { red, green, blue, yellow, white, black } Colors;

Colors col;
integer a, b;

a = blue * 3;
col = yellow;
b = col + green;
```

从前面的声明中，blue 的数值为 2。这个例子将 a 赋值为 6（2*3），并将 b 赋值为 4（3+1）。

枚举变量或标识符作为表达式的一部分时，会自动转换为枚举声明的基本类型（显式或使用 int 作为默认值）。对于分配给枚举变量的表达式，如果表达式的类型与变量的枚举类型不等效，则需要显式转换。

将表达式转换为枚举类型将导致将表达式转换为其基本类型，而不检查值的有效性（除非使用 6.24.2 中描述的动态转换）。

```verilog
typedef enum {Red, Green, Blue} Colors;
typedef enum {Mo,Tu,We,Th,Fr,Sa,Su} Week;
Colors C;
Week W;
int I;

C = Colors'(C+1); // C 转换为整数，然后加 1，然后转换回 Colors 类型

C = C + 1; C++; C+=2; C = I; // 非法，因为它们都是没有转换的表达式赋值

C = Colors'(Su); // 合法；将一个超出范围的值放入 C

I = C + W; // 合法；C 和 W 自动转换为 int
```

### 6.19.5 枚举类型方法
SystemVerilog 包括一组专门的方法，用于在枚举类型的值上进行迭代，这些方法在 6.19.5.1 到 6.19.5.6 中定义。

#### 6.19.5.1 First()
first() 方法的原型如下：
```verilog
function enum first();
```

first() 方法返回枚举的第一个成员的值。

#### 6.19.5.2 Last()
last() 方法的原型如下：
```verilog
function enum last();
```

last() 方法返回枚举的最后一个成员的值。

#### 6.19.5.3 Next()
next() 方法的原型如下：
```verilog
function enum next( int unsigned N = 1 );
```

next() 方法返回从给定变量的当前值开始的第 N 个下一个枚举值（默认为下一个）。当到达枚举的末尾时，将回到枚举的开始。如果给定值不是枚举的成员，则 next() 方法返回枚举的默认初始值（请参见表 6-7）。

#### 6.19.5.4 Prev()
prev() 方法的原型如下：
```verilog
function enum prev( int unsigned N = 1 );
```

prev() 方法返回从给定变量的当前值开始的第 N 个前一个枚举值（默认为前一个）。当到达枚举的开始时，将回到枚举的末尾。如果给定值不是枚举的成员，则 prev() 方法返回枚举的默认初始值（请参见表 6-7）。

#### 6.19.5.5 Num()
num() 方法的原型如下：
```verilog
function int num();
```

num() 方法返回给定枚举中的元素数。

#### 6.19.5.6 Name()
name() 方法的原型如下：
```verilog
function string name();
```

name() 方法返回给定枚举值的字符串表示。如果给定值不是枚举的成员，则 name() 方法返回空字符串。

#### 6.19.5.7 使用枚举类型方法
以下代码片段显示了如何显示枚举的所有成员的名称和值：
```verilog
typedef enum { red, green, blue, yellow } Colors;
Colors c = c.first;
forever begin
    $display( "%s : %d\n", c.name, c );
    if( c == c.last ) break;
    c = c.next;
end
```

## 6.20 常量
常量是有名字的永不改变的数据对象。SystemVerilog 提供了三种编译时常量：`parameter`、`localparam` 和 `specparam`。SystemVerilog 还提供了运行时常量 `const`（见 6.20.6）。

`parameter`、`localparam` 和 `specparam` 常量统称为*参数*常量。

参数常量可以使用字面量初始化。

```verilog
localparam byte colon1 = ":" ;
specparam delay = 10 ; // specparams 用于 specify 块
parameter logic flag = 1 ;
```

SystemVerilog 为设置参数常量的值提供了几种方法。每个参数可以在声明时分配一个默认值。在每个实例中，可以使用以下方法之一覆盖实例化模块、接口或程序的参数的值：
 - 通过有序列表赋值（例如，`m #(value, value) u1 (...);`）（见 23.10.2.1）
 - 通过名称赋值（例如，`m #(.param1(value), .param2(value)) u1 (...);`）（见 23.10.1）
 - 使用层次路径名重新定义每个参数的 `defparam` 语句（见 23.10.1）

注意：`defparam` 语句可能会在将来的版本中删除。请参见 C.4.1。

### 6.20.1 参数声明语法

---
```verilog
local_parameter_declaration ::= // from A.2.1.1
localparam data_type_or_implicit list_of_param_assignments 
| localparam type list_of_type_assignments 
parameter_declaration ::= 
parameter data_type_or_implicit list_of_param_assignments 
| parameter type list_of_type_assignments 
specparam_declaration ::= 
specparam [ packed_dimension ] list_of_specparam_assignments ;
data_type_or_implicit ::= // from A.2.2.1
data_type 
| implicit_data_type 
implicit_data_type ::= [ signing ] { packed_dimension } 
list_of_param_assignments ::= param_assignment { , param_assignment } // from A.2.3
list_of_specparam_assignments ::= specparam_assignment { , specparam_assignment } 
list_of_type_assignments ::= type_assignment { , type_assignment } 
param_assignment ::= // from A.2.4
parameter_identifier { unpacked_dimension } [ = constant_param_expression ]18
specparam_assignment ::= 
specparam_identifier = constant_mintypmax_expression 
| pulse_control_specparam 
type_assignment ::= 
type_identifier [ = data_type ]18
parameter_port_list ::= // from A.1.3
# ( list_of_param_assignments { , parameter_port_declaration } )
| # ( parameter_port_declaration { , parameter_port_declaration } )
| #( )
parameter_port_declaration ::= 
parameter_declaration 
| local_parameter_declaration 
| data_type list_of_param_assignments 
| type list_of_type_assignments 
// 只有在parameter_port_list中，从param_assignment中省略constant_param_expression或从type_assignment中省略data_type才是合法的。但是，在parameter_port_list的localparam声明中省略它们是不合法的。
```
---
语法 6-6—参数声明语法（摘自附录 A）

*list_of_param_assignments* 可以出现在模块、接口、程序、类或包中，或者出现在模块、接口、程序、类的 *parameter_port_list* 中（见 23.2）。如果设计元素的声明使用 *parameter_port_list*（即使是空的），则在声明中直接包含的每个 *parameter_declaration* 中，`parameter` 关键字应该是 `localparam` 关键字的同义词（见 6.20.4）。出现在类体中的所有 *param_assignments* 都将成为 `localparam` 声明，而不管 *parameter_port_list* 的存在与否。出现在 `generate` 块、包或编译单元范围内的所有 *param_assignments* 都将成为 localparam 声明。

`parameter` 关键字可以在参数端口列表中省略。例如：
```verilog
class vector #(size = 1); // size 是参数在参数端口列表中
    logic [size-1:0] v;
endclass

interface simple_bus #(AWIDTH = 64, type T = word) // 参数端口列表
                      (input logic clk) ; // 端口列表
...
endinterface
```

在参数常量列表中，一个参数可以依赖于先前的参数。在下面的声明中，第二个参数的默认值取决于第一个参数的值。第三个参数是一个类型，第四个参数是该类型的值。
```verilog
module mc #(int N = 5, M = N*16, type T = int, T x = 0)
 ( ... );
...
endmodule
```

在设计元素的参数中未指定默认值时，必须在该设计元素的每个实例化中指定覆盖参数值（见 23.10）。此外，如果设计元素的参数中未指定默认值，则工具不得隐式实例化该设计元素（见 23.3、23.4 和 24.3）。如果设计元素的参数中未指定默认值，则必须在该类的每个特化中指定覆盖参数值（见 8.25）。

```verilog
class Mem #(type T, int size); 
    T words[size];
    ...
endclass

typedef Mem#(byte, 1024) Kbyte;
```

### 6.20.2 值参数
参数常量可以具有*类型*规范和*范围*规范。参数的类型和范围规范应符合以下规则：
 - 没有类型或范围规范的参数声明应默认为参数赋值后的最终值的类型和范围。如果表达式是实数，则参数是实数。如果表达式是整数，则参数是相同大小的 `logic` 向量，范围为 [size-1:0]。
 - 具有范围规范但没有类型规范的参数应具有参数声明的范围，并且应为无符号。不应受到值覆盖的影响。
 - 具有类型规范但没有范围规范的参数应为指定的类型。有符号参数应默认为参数赋值后的最终值的范围。不应受到值覆盖的影响。
 - 具有有符号类型规范和范围规范的参数应为有符号，并且应具有声明的范围。不应受到值覆盖的影响。
 - 没有范围规范但具有有符号类型规范或没有类型规范的参数应具有隐含范围，lsb 等于 0，msb 等于参数赋值后的最终值的大小减 1。
 - 没有范围规范，具有有符号类型规范或没有类型规范的参数，其最终值未定义大小，应具有隐含范围，*lsb* 等于 0，*msb* 等于至少为 31 的实现相关值。

在对参数进行赋值或覆盖时，右侧表达式的类型必须与声明的类型兼容（见 6.22.3）。

在 6.12.2 中描述的实数和整数值之间的转换规则也适用于参数。

参数的整数类型的位选择和部分选择应该是允许的（见 6.11.1）。

值参数（`parameter`、`localparam` 或 `specparam`）只能设置为字面值、值参数或本地参数、genvars、枚举名称或这些的常量函数的表达式。包引用是允许的。不允许层次名称。specparam 也可以设置为包含一个或多个 `specparams` 的表达式。

例如：
```verilog
parameter msb = 7; // 将 msb 定义为常量值 7
parameter e = 25, f = 9; // 定义两个常量数字
parameter r = 5.7; // 将 r 声明为实数参数
parameter byte_size = 8,
byte_mask = byte_size - 1;
parameter average_delay = (r + f) / 2;
parameter signed [3:0] mux_selector = 0;
parameter real r1 = 3.5e17;
parameter p1 = 13'h7e;
parameter [31:0] dec_const = 1'b1; // 值转换为 32 位
parameter newconst = 3'h4; // 隐含范围为 [2:0]
parameter newconst = 4; // 隐含范围至少为 [31:0]
```

参数也可以声明为聚合类型，例如未打包数组或未打包结构。聚合参数必须作为一个整体赋值或覆盖；不允许单独赋值或覆盖聚合参数的各个成员。但是，可以在表达式中使用聚合参数的单个成员。例如：
```verilog
parameter logic [31:0] P1 [3:0] = '{ 1, 2, 3, 4 } ; // 未打包数组的参数声明

initial begin
    if ( P1[2][7:0] ) ... // 使用数组的单个元素的部分选择
```

#### 6.20.2.1 $ 参数值
`$` 可以分配给整数类型的参数。分配给 `$` 的参数只能在 `$` 可以作为字面常量的地方使用。

例如，`$` 表示无界范围规范，其中上限索引可以是任何整数。
```verilog
parameter r2 = $;
property inq1(r1,r2);
    @(posedge clk) a ##[r1:r2] b ##1 c |=> d;
endproperty
assert inq1(3);
```

提供了一个系统函数来测试常量是否为 `$`。系统函数的语法如下：
```verilog
$isunbounded(constant_expression);
```

如果 *constant_expression* 是无界的，则 `$isunbounded` 返回 true。通常，`$isunbounded` 将用作生成语句中的条件。

下面的示例说明了在参数化范围的情况下使用 `$` 编写简洁属性的好处。示例中的检查器验证由信号 en 驱动的总线在指定的最小（min_quiet）和最大（max_quiet）安静时间内保持为 0。

注意：`$isunbounded` 函数用于检查实际参数的有效性。
```verilog
interface quiet_time_checker #(parameter min_quiet = 0,
                               parameter max_quiet = 0)
                             (input logic clk, reset_n, logic [1:0]en); 
    generate
        if ( max_quiet == 0) begin
            property quiet_time;
                @(posedge clk) reset_n |-> ($countones(en) == 1);
            endproperty
            a1: assert property (quiet_time);
        end
        else begin
            property quiet_time;
                @(posedge clk)
                    (reset_n && ($past(en) != 0) && en == 0)
                    |->(en == 0)[*min_quiet:max_quiet]
                ##1 ($countones(en) == 1);
            endproperty
            a1: assert property (quiet_time);
        end
        if ((min_quiet == 0) && ($isunbounded(max_quiet)))
            $display(warning_msg);
    endgenerate
endinterface

quiet_time_checker #(0, 0) quiet_never (clk,1,enables);
quiet_time_checker #(2, 4) quiet_in_window (clk,1,enables);
quiet_time_checker #(0, $) quiet_any (clk,1,enables);
```

下面的另一个示例说明了通过测试 `$`，可以根据需求配置属性。当参数 max_cks 无限时，不需要检查 expr 是否为 false。

```verilog
interface width_checker #(parameter min_cks = 1, parameter max_cks = 1)
                        (input logic clk, reset_n, expr);
    generate
        if ($isunbounded(max_cks)) begin
            property width;
                @(posedge clk)
                    (reset_n && $rose(expr)) |-> (expr [* min_cks]);
            endproperty
            a2: assert property (width);
        end
        else begin
            property assert_width_p;
                @(posedge clk) 
                    (reset_n && $rose(expr)) |-> (expr[* min_cks:max_cks])
                        ##1 (!expr);
            endproperty
            a2: assert property (width);
        end
    endgenerate
endinterface

width_checker #(3, $) max_width_unspecified (clk,1,enables);
width_checker #(2, 4) width_specified (clk,1,enables);
```

### 6.20.3 类型参数
参数常量还可以指定数据类型，允许模块、接口或程序拥有端口和数据对象，其类型为每个实例设置。

```verilog
module ma #( parameter p1 = 1, parameter type p2 = shortint )
          (input logic [p1:0] i, output logic [p1:0] o);
    p2 j = 0; //  j 的类型由参数指定，为 shortint，否则重新定义
    always @(i) begin
        o = i; 
        j++; 
    end
endmodule

module mb;
    logic [3:0] i,o;
    ma #(.p1(3), .p2(int)) u1(i,o); // 重新定义 p2 为 int
endmodule
```

赋值给或覆盖类型参数的值必须是数据类型。

数据类型参数（`parameter type`）可以仅用来指定数据类型。包引用是允许的。不允许层次名称。

用 `defparam` 语句覆盖类型参数是不合法的。

### 6.20.4 本地参数
本地参数与参数相同，只是不能直接通过 `defparam` 语句（见 23.10.1）或实例参数值赋值（见 23.10.2）进行修改。本地参数可以分配包含参数的常量表达式（见 11.2.1），这些参数*可以*通过 `defparam` 语句或实例参数值赋值进行修改。

与非本地参数不同，本地参数可以在生成块、包、类体或编译单元范围内声明。在这些上下文中，`parameter` 关键字应该是 `localparam` 关键字的同义词。

本地参数可以在模块的 *parameter_port_list* 中声明。出现在这样的列表中的任何参数声明在 `localparam` 关键字和下一个 `parameter` 关键字（或列表结束，如果没有下一个 `parameter` 关键字）之间应该是本地参数。在这样的列表中的任何其他参数声明应该是可以被覆盖的非本地参数，如 23.10 中所述。

### 6.20.5 指定参数
关键字 `specparam` 声明了一种特殊类型的参数，仅用于提供时间和延迟值，但可以出现在任何未分配给参数的表达式中，也不是声明的范围规范的一部分。指定参数（也称为 *specparams*）允许在 specify 块（见 30 章）中和主模块体中使用。

在指定块之外声明的指定参数在引用之前应该声明。分配给指定参数的值可以是任何常量表达式。指定参数可以用作后续指定参数声明的常量表达式的一部分。与 `parameter` 常量不同，指定参数不能从语言内部修改，但可以通过 SDF 注释（见 32 章）进行修改。

指定参数和 `parameter` 常量不可互换。此外， `parameter` 和 `localparam` 不得分配包含任何指定参数的常量表达式。表 6-11 总结了两种参数声明之间的区别。

表 6-11—specparams 和 parameters 之间的区别
| Specparams（指定参数） | Parameters |
| -------------------------------- | ---------- |
| 使用关键字 `specparam` | 使用关键字 `parameter` |
| 应在模块或指定块*内*声明 | 应在指定块*外*声明 |
| 只能在模块或 specify 块内使用 | 不能在 specify 块内使用 |
| 可以分配 specparams 和 parameters | 不能分配 specparams |
| 使用 SDF 注释覆盖值 | 使用 `defparam` 或实例声明参数值传递覆盖值 |

一个指定参数可以有一个范围规范。指定参数的范围规范应符合以下规则：
 - 没有范围规范的 `specparam` 声明应默认为指定参数赋值后的最终值的范围。
 - 具有范围规范的 `specparam` 应具有指定参数声明的范围。范围规范不应受到值覆盖的影响。

例如：
```verilog
specify
    specparam tRise_clk_q = 150, tFall_clk_q = 200;
    specparam tRise_control = 40, tFall_control = 50;
endspecify
```

在上面的示例中，指定了四个指定参数。第一行声明了名为 tRise_clk_q 和 tFall_clk_q 的指定参数，值分别为 150 和 200；第二行声明了 tRise_control 和 tFall_control 指定参数，值分别为 40 和 50。

```verilog
module RAM16GEN ( output [7:0] DOUT,
                  input [7:0] DIN,
                  input [5:0] ADR, 
                  input WE, CE);
    specparam dhold = 1.0;
    specparam ddly = 1.0;
    parameter width = 1;
    parameter regsize = dhold + 1.0; // I非法：不能将 specparams 分配给 parameters
endmodule
```

### 6.20.6 Const 常量
`const` 形式的常量与 `localparam` 常量不同，`localparam` 在建立期间设置，而 `const` 可以在仿真期间设置，例如在自动任务中。

使用 `const` 关键字声明的静态常量可以设置为字面量、参数、本地参数、genvars、枚举名称、这些的常量函数或其他常量。允许层次名称，因为使用 `const` 关键字声明的常量在建立后计算。

```verilog
const logic option = a.b.c ;
```

使用 `const` 关键字声明的自动常量可以设置为任何不带 `const` 关键字的合法表达式。

可以使用 `const` 关键字声明类的实例（对象句柄）。

```verilog
const class_name object = new(5,3);
```

换句话说，对象的行为类似于不能写入的变量。传递给 new 方法的参数应该是常量表达式（见 11.2.1）。对象的成员可以写入（除了声明为 const 的成员）。

## 6.21 作用域和生命周期
声明在模块、程序、接口、检查器、任务或函数之外的变量是编译单元的局部变量，并具有静态生命周期（在整个仿真期间存在）。这大致相当于在函数之外声明的 C 静态变量，这些变量是文件内部的。在模块、接口、程序或检查器内部声明的变量，但在任务、进程或函数之外，是局部的，并具有静态生命周期。

在静态任务、函数或块内部声明的变量是局部的，并默认具有静态生命周期。在静态任务、函数或块内部声明的特定变量可以显式声明为自动的。这样的变量在调用或块的生命周期内初始化（也见 6.8 中的变量初始化）。这大致相当于在函数中声明的 C 自动变量。

任务和函数可以声明为 `automatic`。在自动任务、函数或块内部声明的变量是局部的，并默认具有调用或块的生命周期，并在每次进入调用或块时初始化（也见 6.8 中的变量初始化）。自动块是默认情况下声明为自动的块。在自动任务、函数或块内部声明的特定变量可以显式声明为静态的。这样的变量具有静态生命周期。这大致相当于在函数中声明的 C 静态变量。

fork-join 块的生命周期应包括由块生成的所有进程的执行。包围任何 fork-join 块的作用域包括 fork-join 块的生命周期。

变量声明应在对该变量的任何简单引用（非层次引用）之前。变量声明应在过程块内的任何语句之前。变量也可以在无名块中声明。这些变量对无名块及其下面的任何嵌套块可见。不应使用层次引用通过名称访问这些变量。

```verilog
module msl;
    int st0; // 静态
    initial begin
        int st1; // 静态
        static int st2; // 静态
        automatic int auto1; // 自动
    end
    task automatic t1();
        int auto2; // 自动
        static int st3; // 静态
        automatic int auto3; // 自动
    endtask
endmodule
```

在静态任务、函数或过程块内部声明的变量默认具有静态生命周期和局部作用域。但是，当在静态变量的声明中指定初始化值时，应显式需要 static 关键字，以指示用户的意图，即在仿真开始时仅执行该初始化一次。在不合法声明变量为自动时，static 关键字是可选的。例如：
```verilog
module top_legal;
    int svar1 = 1; // static 关键字可选
    initial begin
        for (int i=0; i<3; i++) begin
            automatic int loop3 = 0; // 每次循环都会执行
            for (int j=0; j<3; j++) begin
                loop3++;
                $display(loop3);
            end
        end // 打印 1 2 3 1 2 3 1 2 3
        for (int i=0; i<3; i++) begin
            static int loop2 = 0; // 在时间 0 之前执行一次
            for (int j=0; j<3; j++) begin
                loop2++;
                $display(loop2);
            end
        end // 打印 1 2 3 4 5 6 7 8 9
    end
endmodule : top_legal

module top_illegal; // 不应编译
    initial begin
        int svar2 = 2; // 需要 static/automatic 以显示意图
        for (int i=0; i<3; i++) begin
            int loop3 = 0; // 非法语句
            for (int i=0; i<3; i++) begin
                loop3++;
                $display(loop3);
            end
        end
    end
endmodule : top_illegal
```

可以使用可选限定符来指定在模块、函数、块或程序中定义的任务、函数或块中声明的所有变量的默认生命周期。生命周期限定符是 `automatic` 或 `static`。默认生命周期是 `static`。

```verilog
program automatic test ;
    int i; // 不在过程块内 - 静态
    task t ( int a ); // t 中的参数和变量是自动的，除非显式声明为静态
    ...
    endtask
endprogram
```

可以对静态变量进行层次引用，除非变量声明在无名块内。这包括在自动任务和函数中声明的静态变量。

类方法（见第 8 章）和声明的 for 循环变量（见 12.7.1）默认为自动，无论它们所在的作用域的生命周期属性如何。

不得使用非阻塞、连续或过程连续赋值写入自动变量或动态大小数组变量的元素。不得使用连续或过程连续赋值写入非静态类属性。对自动变量和动态变量的元素或成员的引用应限制在过程块中。

有关任务和函数，请参见第 13 章。

## 6.22 类型兼容性
一些结构和操作需要操作数具有一定级别的类型兼容性才能合法。有五个级别的类型兼容性，以下是正式定义的：匹配、等效、赋值兼容、强制转换兼容和不等效。

SystemVerilog 不要求在此定义中定义相同类型的类别，因为 SystemVerilog 语言中没有要求。例如，如下所定义，`int` 可以在任何语法上合法的地方与 `bit signed [31:0]` 互换。用户可以通过使用 `$typename` 系统函数（见 20.6.1）或通过使用 PLI 来定义自己的类型标识符的级别。

数据类型标识符的范围应包括层次实例范围。换句话说，每个在实例内部声明的用户定义类型创建一个唯一的类型。要在同一模块、接口、程序或检查器的多个实例之间具有类型匹配或等效，必须在编译单元范围内的声明模块、接口、程序或检查器的声明之上声明类、枚举、未打包结构或未打包联合类型，或从包导入。对于类型匹配，即使是打包结构和打包联合类型，这也是正确的。

### 6.22.1 匹配类型
两个数据类型应定义为*匹配数据类型*，使用以下归纳定义。如果两个数据类型不符合以下定义，则应定义为不匹配。
 - `a)` 任何内置类型与每个其他自身的出现匹配，无论在哪个范围内。
 - `b)` 重命名内置或用户定义类型的简单 typedef 或类型参数覆盖匹配该范围内的类型标识符。

```verilog
typedef bit node; // 'bit' 和 'node' 是匹配类型
typedef type1 type2; // 'type1' 和 'type2' 是匹配类型
```

 - `c)` 匿名枚举、结构或联合类型仅在同一声明语句内声明的数据对象之间匹配，不匹配其他数据类型。

```verilog
struct packed {int A; int B;} AB1, AB2; // AB1, AB2 是匹配类型
struct packed {int A; int B;} AB3; // AB3 的类型不匹配 AB1 的类型
```

 - `d)` 用于枚举、结构、联合或类类型的 typedef 与该数据类型的数据对象在类型标识符的范围内声明的数据对象匹配。

```verilog
typedef struct packed {int A; int B;} AB_t;
AB_t AB1; AB_t AB2; // AB1 和 AB2 是匹配类型
typedef struct packed {int A; int B;} otherAB_t;
otherAB_t AB3; // AB3 的类型不匹配 AB1 或 AB2 的类型
```

 - `e)` 一个没有预定义宽度的简单位向量类型和一个具有预定义宽度的简单位向量类型匹配，如果两者都是 2 状态或 4 状态，都是有符号或无符号，都具有相同的宽度，并且没有预定义宽度的简单位向量类型的范围是 [width-1:0]。

```verilog
typedef bit signed [7:0] BYTE; // 匹配 byte 类型
typedef bit signed [0:7] ETYB; // 不匹配 byte 类型
```

 - `f)` 两个数组类型匹配，如果它们都是打包的或都是未打包的，都是相同类型的数组（固定大小、动态、关联或队列），具有匹配的索引类型（对于关联数组），并且具有匹配的元素类型。固定大小数组还应具有相同的左和右范围边界。请注意，多维数组的元素类型本身就是一个数组类型。

```verilog
typedef byte MEM_BYTES [256];
typedef bit signed [7:0] MY_MEM_BYTES [256]; // MY_MEM_BYTES 匹配 MEM_BYTES

typedef logic [1:0] [3:0] NIBBLES;
typedef logic [7:0] MY_BYTE; // MY_BYTE 和 NIBBLES 不是匹配类型

typedef logic MD_ARY [][2:0];
typedef logic MD_ARY_TOO [][0:2]; // 不匹配 MD_ARY
```

 - `g)` 明确添加有 `signed` 或 `unsigned` 修饰符到不改变其默认签名的类型创建一个匹配没有显式签名规范的类型。

```verilog
typedef byte signed MY_CHAR; // MY_CHAR 匹配 byte 类型
```

 - `h)` 在包中声明的 enum、struct、union 或类类型的 typedef 总是与自身匹配，而不管将该类型导入到哪个作用域。

### 6.22.2 等效类型
两个数据类型应定义为*等效数据类型*，使用以下归纳定义。如果两个数据类型不符合以下定义，则应定义为不等效。
 - `a)` 如果两个类型匹配，则它们是等效的。
 - `b)` 匿名枚举、未打包结构或未打包联合类型仅在同一声明语句内声明的数据对象之间是等效的，不等效其他数据类型。

```verilog
struct {int A; int B;} AB1, AB2; // AB1, AB2 是等效类型
struct {int A; int B;} AB3; // AB3 不等效于 AB1
```

 - `c)` 打包的数组、打包的结构、打包的联合和内置整数类型是等效的，如果它们包含相同数量的总位数，都是 2 状态或 4 状态，都是有符号或无符号。

注意：如果打包结构或联合的任何位是 4 状态，则整个结构或联合被视为 4 状态。

```verilog
typedef bit signed [7:0] BYTE; // 等效于 byte 类型
typedef struct packed signed {bit[3:0] a, b;} uint8; // 等效于 byte 类型
```

 - `d)` 未打包的固定大小的数组类型是等效的，如果它们具有等效的元素类型和相同的大小；实际范围边界可能不同。请注意，多维数组的元素类型本身就是一个数组类型。

```verilog
bit [9:0] A [0:5];
bit [1:10] B [6];
typedef bit [10:1] uint10;
uint10 C [6:1]; // A, B 和 C 是等效类型
typedef int anint [0:0]; // anint 不等效于 int
```

 - `e)` 动态数组、关联数组和队列类型是等效的，如果它们是相同类型的数组（动态、关联或队列），具有等效的索引类型（对于关联数组）和等效的元素类型。

下面的例子假定在一个编译单元中，尽管包声明不必在同一单元中：

```verilog
package p1;
    typedef struct {int A;} t_1;
endpackage

typedef struct {int A;} t_2;

module sub();
    import p1::t_1;
    parameter type t_3 = int;
    parameter type t_4 = int;
    typedef struct {int A;} t_5;
    t_1 v1; t_2 v2; t_3 v3; t_4 v4; t_5 v5;
endmodule
module top();
    typedef struct {int A;} t_6;
    sub #(.t_3(t_6)) s1 ();
    sub #(.t_3(t_6)) s2 ();

    initial begin
        s1.v1 = s2.v1; // 合法——都是来自包 p1（规则 8）
        s1.v2 = s2.v2; // 合法——都是来自 $unit（规则 4）
        s1.v3 = s2.v3; // 合法——都是来自 top（规则 2）
        s1.v4 = s2.v4; // 合法——都是 int（规则 1）
        s1.v5 = s2.v5; // 非法——来自 s1 和 s2（规则 4）
    end
endmodule
```

### 6.22.3 赋值兼容
所有等效类型和所有具有定义的隐式转换规则的不等效类型都是*赋值兼容类型*。例如，所有整数类型都是赋值兼容的。赋值兼容类型之间的转换可能涉及数据的截断或舍入导致数据丢失。

未打包数组与某些其他未打包数组是赋值兼容的。未打包数组的赋值兼容性在 7.6 中详细讨论。

兼容性可能只在一个方向。例如，枚举可以转换为整数类型而无需强制转换，但反之则不然。隐式转换规则在 6.24 中定义。

### 6.22.4 强制转换兼容
所有赋值兼容类型，加上所有具有定义的显式转换规则的不等效类型，都是*强制转换兼容类型*。例如，整数类型需要强制转换为枚举类型。

显式转换规则在 6.24 中定义。

### 6.22.5 不等效类型
*不等效类型* 包括所有剩余的不等效类型，这些类型没有定义的隐式或显式转换规则。类句柄、接口类句柄和 chandles 与所有其他类型都是不等效的。

### 6.22.6 匹配 nettypes
 - `a)` 一个 nettype 与自身和在 nettype 类型标识符的范围内声明的使用该 nettype 声明的 nets 匹配。
 - `b)` 重命名用户定义 nettype 的简单 nettype 匹配该用户定义 nettype 在 nettype 标识符的范围内声明的 nets。

```verilog
nettype nettypeid1 nettypeid2; // 为 nettype nettypeid1 声明另一个名称 nettypeid2
```

## 6.23 类型操作符
`type` 操作符提供了一种引用表达式的数据类型的方法。类型引用可以像类型名称或本地类型参数一样使用，例如，在转换、数据对象声明和类型参数赋值和覆盖中。它还可以用于与其他类型引用进行相等性/不等性和 case 相等性/不等性比较，这样的比较被认为是常量表达式（见 11.2.1）。当类型引用用于线网声明时，它应该在线网类型关键字之前；当它用于变量声明时，它应该在 `var` 关键字之前。

```verilog
var type(a+b) c, d;
c = type(i+3)'(v[15:0]);
```

应用于表达式的 `type` 操作符应表示该表达式的自决结果类型。不应计算表达式，也不应包含任何层次引用或对动态对象的元素的引用。

类型操作符也可以应用于数据类型。

```verilog
localparam type T = type(bit[12:0]);
```

当类型引用用于等式/不等式或 case 等式/不等式比较时，它只能与另一个类型引用进行比较。在这样的比较中，如果且仅当它们引用的类型匹配时，两个类型引用应被认为是相等的（见 6.22.1）。

```verilog
bit [12:0] A_bus, B_bus;
parameter type bus_t = type(A_bus);
generate
    case (type(bus_t))
        type(bit[12:0]): addfixed_int #(bus_t) (A_bus,B_bus);
        type(real): add_float #(type(A_bus)) (A_bus,B_bus);
    endcase
endgenerate
```

## 6.24 类型转换
### 6.24.1 转换操作符
可以使用cast（`'`）操作更改数据类型。转换操作的语法如 6-7 所示。

---
```verilog
constant_cast ::= // from A.8.4
casting_type ' ( constant_expression )
cast ::= 
casting_type ' ( expression )
casting_type ::= simple_type | constant_primary | signing | string | const // from A.2.2.1
simple_type ::= integer_type | non_integer_type | ps_type_identifier | ps_parameter_identifier
```
---

语法 6-7—转换（摘自附录 A）

在静态转换中，要转换的表达式应该用括号括起来，括号前面有转换类型和一个撇号。如果表达式与转换类型兼容，则转换应返回一个变量的值，该变量在分配表达式后将保持转换类型的值。如果表达式与转换类型不兼容，则如果转换类型是枚举类型，则行为应如 6.19.4 中所述，如果转换类型是位流类型，则行为应如 6.24.3 中所述。

```verilog
int'(2.0 * 3.0)
shortint'({8'hFA,8'hCE})
```

因此，在以下示例中，如果表达式 expr_1 和 expr_2 与数据类型 cast_t1 和 cast_t2 赋值兼容，则

```verilog
A = cast_t1'(expr_1) + cast_t2'(expr_2);
```

与

```verilog
cast_t1 temp1;
cast_t2 temp2;
temp1 = expr_1;
temp2 = expr_2;
A = temp1 + temp2;
```

是相同的。

因此，如果定义了，则隐式转换（例如，temp1 = expr1）给出与相应的显式转换（cast_t1'(expr1)）相同的结果。

如果转换类型是具有正整数值的常量表达式，则括号中的表达式应填充或截断到指定的大小。如果指定的大小为零或负，则应出错。

例如：
    
```verilog
17'(x - 2)

parameter P = 16;
(P+1)'(x – 2)
```

符号性也可以改变。

```verilog
signed'(x)
```

当改变大小或符号时，括号内的表达式应为整数值。

当改变大小时，转换应返回具有单一 [n-1:0] 维度的打包数组类型在被赋值表达式后将持有的值，其中 n 是转换大小。符号性应保持不变，即，结果的符号性应为括号内表达式的自决符号性。如果括号内表达式是 2 状态，则数组元素应为 `bit` 类型，否则应为 `logic` 类型。

当改变符号时，转换应返回具有单一 [n-1:0] 维度的打包数组类型在被赋值表达式后将持有的值，其中 n 是表达式要转换的位数（`$bits(expression)`）。结果的符号性应为转换类型指定的符号性。如果括号内表达式是 2 状态，则数组元素应为 `bit` 类型；否则，应为 `logic` 类型。

注意：`$signed()` 和 `$unsigned()` 系统函数（见 11.7）返回与 `signed'()` 和 `unsigned'()` 相同的结果。

例如：

```verilog
logic [7:0] regA;
logic signed [7:0] regS;

regA = unsigned'(-4); // regA = 8'b11111100
regS = signed'(4'b1100); // regS = -4
```

表达式可以使用 `const` 转换为常量。

```verilog
const'(x)
```

当将表达式转换为常量时，要转换的表达式的类型应保持不变。唯一的效果是将该值视为已用于定义表达式类型的常量。

当转换为预定义类型时，转换的前缀应为预定义类型关键字。当转换为用户定义类型时，转换的前缀应为用户定义类型标识符。

当将 `shortreal` 转换为 `int` 或使用转换或赋值将其转换为 32 位时，其值将被四舍五入（见 6.12）。因此，转换可能会丢失信息。要将 shortreal 转换为其底层位表示形式而不丢失信息，请使用 20.5 中定义的 `$shortrealtobits`。要将 shortreal 值的位表示形式转换为 `shortreal`，请使用 20.5 中定义的 `$bitstoshortreal`。

结构可以转换为保留位模式的位。换句话说，它们可以转换回相同值而不会丢失任何信息。当未打包数据转换为打包表示时，打包表示中的数据顺序是这样的，即结构中的第一个字段占用 MSB。效果与数据项（`struct` 字段或数组元素）按顺序连接相同。未打包结构或数组中的元素的类型应为打包表示中的有效类型，以便转换为任何其他类型，无论是打包还是未打包。

不需要显式转换两个打包类型之间的转换，因为它们隐式转换为整数值，但是工具可以使用转换来执行更强的类型检查。

以下示例演示了如何使用 `$bits` 来获取结构的位大小（`$bits` 系统函数在 20.6.2 中讨论），这有助于将结构转换为打包数组：

```verilog
typedef struct { 
    bit isfloat; 
    union { int i; shortreal f; } n; // 匿名类型 
} tagged_st; // 命名结构

typedef bit [$bits(tagged_st) - 1 : 0] tagbits; // 上面定义的 tagged_st

tagged_st a [7:0]; // 未打包结构数组

tagbits t = tagbits'(a[3]); // 将结构转换为位数组
a[4] = tagged_st'(t); // 将位数组转换回结构
```

请注意，`bit` 数据类型会丢失 X 值。如果要保留这些值，则应使用 `logic` 类型。

联合的位大小是其最大成员的大小。`logic` 的大小为 1。

函数 `$itor`、`$rtoi`、`$bitstoreal`、`$realtobits`、`$signed` 和 `$unsigned` 也可用于执行类型转换（见第 20 章）。

