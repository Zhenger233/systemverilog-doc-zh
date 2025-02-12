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

声明为互连（互连网或端口）的网或端口表示无类型或通用网。这种网或端口仅能表达网端口和终端连接，并且不得在任何过程性上下文或任何连续或过程性连续赋值中使用。互连网或端口不得在除了所有网或端口都是互连网的 net_lvalue 表达式之外的任何表达式中使用。即使数组中的不同位被解析为不同的网类型，也应将互连数组视为有效，如下面的示例所示。可以在互连 net_lvalue 中指定 net_alias 语句。有关互连网的端口和终端连接规则，请参见 23.3.3.7.1 和 23.3.3.7.2。

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

以下简单示例用于说明互连网的有用性。该示例包含一个顶层模块（top），该模块实例化一个刺激模块（driver）和一个比较器模块（cmp）。此配置旨在比较两个元素并确定它们是否相等。根据两个不同版本的配置，由两个不同的配置块描述：一个用于实数值，一个用于逻辑值。通过使用无类型的互连网，我们可以在不必更改测试台本本身的情况下，使用相同的测试台本与两个配置。互连网 aBus 从其连接的类型中获取数据类型。

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
