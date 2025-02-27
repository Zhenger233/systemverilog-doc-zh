# 19. 功能覆盖率
## 19.1 概述
本章描述以下内容：
 - 定义覆盖组
 - 定义覆盖点
 - 定义交叉覆盖
 - 覆盖选项
 - 覆盖系统任务和系统函数
 - 覆盖计算

## 19.2 总览
功能验证占用了设计和验证复杂系统所需资源的大部分。通常，验证必须全面而没有冗余的工作。为了最小化浪费的工作，覆盖率被用作指导验证资源的指南，通过识别设计的已测试和未测试部分。

覆盖率被定义为已满足的验证目标的百分比。它被用作评估验证项目进展的指标，以减少在验证设计中花费的模拟周期数。

广义上说，有两种类型的覆盖率指标：可以从设计代码中自动提取的指标，如代码覆盖率，以及用户指定的指标，以将验证环境与设计意图或功能绑定。后者称为 *功能覆盖率*，是本章的主题。

功能覆盖率是一个用户定义的度量，用于衡量测试计划中的特性所列举的设计规范的多少已经被执行。它可以用来衡量是否已观察、验证和测试了有趣的场景、边界情况、规范不变量或其他适用的设计条件。

功能覆盖率的关键方面如下：
 - 它是用户指定的，不是从设计中自动推断出来的。
 - 它基于设计规范（即其意图），因此与实际设计代码或其结构无关。

因为它完全由用户指定，功能覆盖率需要更多的前期工作（必须有人编写覆盖模型）。功能覆盖率还需要更有结构化的验证方法。虽然功能覆盖率可以缩短整体验证工作量并产生更高质量的设计，但它的缺点可能会阻碍其采用。

SystemVerilog 功能覆盖率扩展解决了这些缺点，提供了易于指定功能覆盖率模型的语言构造。这种规范可以由 SystemVerilog 模拟引擎高效执行，从而实现覆盖率数据操作和分析工具，加快高质量测试的开发。改进的测试集可以执行更多的边界情况和所需的场景，而不需要冗余工作。

SystemVerilog 功能覆盖率构造使以下功能成为可能：
 - 变量和表达式的覆盖率，以及它们之间的交叉覆盖
 - 自动和用户定义的覆盖率箱
 - 将箱与值集、转换或交叉乘积相关联
 - 在多个级别上的过滤条件
 - 事件和序列自动触发覆盖率采样
 - 过程激活和查询覆盖率
 - 可选指令以控制和调节覆盖率

## 19.3 定义覆盖模型：覆盖组
`covergroup` 构造封装了覆盖模型的规范。每个 `covergroup` 规范可以包括以下组件：
 - 同步覆盖点采样的时钟事件
 - 一组覆盖点
 - 覆盖点之间的交叉覆盖
 - 可选的形式参数
 - 覆盖选项

`covergroup` 构造是用户定义的类型。类型定义只需编写一次，可以在不同的上下文中创建多个该类型的实例。与 class 类似，一旦定义，可以通过 `new()` 操作符创建 `covergroup` 实例。`covergroup` 可以在包、模块、程序、接口、检查器或类中定义。
---
```verilog
covergroup_declaration ::= // from A.2.11
covergroup covergroup_identifier [ ( [ tf_port_list ] ) ] [ coverage_event ] ;
{ coverage_spec_or_option } 
endgroup [ : covergroup_identifier ] 
coverage_spec_or_option ::= 
{attribute_instance} coverage_spec 
| {attribute_instance} coverage_option ;
coverage_option ::= 
option.member_identifier = expression 
| type_option.member_identifier = constant_expression 
coverage_spec ::= 
cover_point 
| cover_cross 
coverage_event ::= 
clocking_event 
| with function sample ( [ tf_port_list ] )
| @@( block_event_expression )
block_event_expression ::= 
block_event_expression or block_event_expression 
| begin hierarchical_btf_identifier 
| end hierarchical_btf_identifier 
hierarchical_btf_identifier ::= 
hierarchical_tf_identifier 
| hierarchical_block_identifier 
| [ hierarchical_identifier. | class_scope ] method_identifier 
```
---
语法 19-1—覆盖组语法（摘自附录 A）

与覆盖组声明相关联的标识符定义了覆盖模型的名称。使用此名称，可以创建任意数量的覆盖模型实例。例如：
```verilog
covergroup cg; ... endgroup
cg cg_inst = new;
```

上面的示例定义了一个名为 `cg` 的覆盖组。一个名为 `cg_inst` 的实例被声明为 `cg` 并使用 `new` 操作符创建。

覆盖组可以指定一个可选的参数列表，如 13.5 中所述。当覆盖组指定一组形式参数时，其实例必须向 `new` 操作符提供所有未默认的实际参数。实际参数在执行 `new` 操作符时进行评估。`ref` 参数允许每个覆盖组实例采样不同的变量。输入参数不会跟踪其参数的值；它们将使用传递给 `new` 操作符的值。

`output` 或 `inout` 作为形式参数是非法的。由于覆盖组不能修改 `new` 操作符的任何参数，因此 `ref` 参数将被视为只读 `const ref` 参数。覆盖组的形式参数不能使用层次名称访问（形式参数不能在覆盖组声明外部访问）。

如果指定了时钟事件，则定义了采样覆盖点的事件。因为它在覆盖组的范围内，时钟事件可以基于覆盖组的 `ref` 参数。如果自动变量通过引用传递，行为是未定义的。如果未指定时钟事件，则用户必须通过内置的 `sample()` 方法（见 19.8）以过程方式触发覆盖采样。预定义的 `sample()` 方法不接受参数；但是，用户可以通过指定带有参数列表的 `sample` 方法作为触发函数来覆盖此行为（见 19.8.1）。如果覆盖的 `sample()` 方法指定了一组形式参数，则每次调用 `sample()` 方法都必须提供所有未默认的实际参数。如果 coverage_event 被省略，则覆盖组应指定预定义的 `sample()` 方法。

可选地，可以使用 `strobe` 选项来修改采样行为。当未设置 `strobe` 选项（默认情况下），覆盖点在时钟事件发生时立即采样，就好像触发事件的进程调用内置的 `sample()` 方法一样。如果时钟事件在一个时间步中发生多次，则覆盖点也将被多次采样。`strobe` 选项（见 19.7.1）可用于指定覆盖点在 Postponed 区域中采样，从而过滤多个时钟事件，以便每个时间槽只采样一次。`strobe` 选项仅适用于由时钟事件触发的采样调度。它不会对过程调用内置的 `sample()` 方法产生影响。

作为时钟事件或采样方法的替代方案，覆盖组接受一个块事件表达式，以指示覆盖采样是由给定命名块、任务、函数或类方法的执行开始或结束触发的。指定以 `begin` 关键字后跟表示命名块、任务、函数或类方法的层次标识符的块事件表达式将在相应块、任务、函数或方法开始执行其第一个语句之前立即触发。指定以 `end` 关键字后跟表示命名块、任务、函数或类方法的层次标识符的块事件表达式将在相应块、任务、函数或方法执行其最后一个语句后立即触发。如果块、任务、函数或方法被禁用，则不会触发执行结束事件。

覆盖组可以包含一个或多个覆盖点。覆盖点可以覆盖变量或表达式。

每个覆盖点包括一组与其采样值或其值转换相关联的箱。与值集相关联的箱称为 *状态箱*，与值转换相关联的箱称为 *转换箱*。箱可以由用户显式定义，也可以由工具自动创建。覆盖点在 19.5 中详细讨论。
```verilog
enum { red, green, blue } color;

covergroup g1 @(posedge clk);
    c: coverpoint color;
endgroup
```

上面的示例定义了覆盖组 `g1`，其中包含一个与变量 `color` 相关的覆盖点。变量 `color` 的值在指示的时钟事件上采样：信号 `clk` 的上升沿。因为覆盖点没有显式定义任何箱，所以工具会自动创建三个箱，每个枚举类型的可能值一个。自动箱在 19.5.3 中描述。

覆盖组还可以指定两个或多个覆盖点或变量之间的交叉覆盖。任何两个以上的变量或先前声明的覆盖点的组合都是允许的。例如：
```verilog
enum { red, green, blue } color;
bit [3:0] pixel_adr, pixel_offset, pixel_hue;

covergroup g2 @(posedge clk);
    Hue: coverpoint pixel_hue;
    Offset: coverpoint pixel_offset;
    AxC: cross color, pixel_adr; // 交叉 2 个变量（隐式声明覆盖点）
    all: cross color, Hue, Offset; // 交叉 1 个变量和 2 个覆盖点
endgroup
```

这个示例创建了覆盖组 `g2`，其中包括两个覆盖点和两个交叉覆盖项。为变量 `pixel_offset` 和 `pixel_hue` 显式定义了覆盖点 `Offset` 和 `Hue`。SystemVerilog 隐式声明了变量 `color` 和 `pixel_adr` 的覆盖点，以便跟踪它们的交叉覆盖。隐式声明的覆盖点在 19.6 中描述。

覆盖组还可以指定一个或多个选项，以控制和调节覆盖数据的结构和收集。覆盖选项可以针对整个覆盖组或覆盖组的特定项（即其任何覆盖点或交叉）指定。一般来说，指定在覆盖组级别的覆盖选项适用于其所有项，除非被它们覆盖。覆盖选项在 19.7 中描述。

## 19.4 在类中使用覆盖组
通过在类定义中嵌入覆盖组，覆盖组提供了一种简单的方法来覆盖类属性的子集。这种覆盖与类集成提供了一个直观和表达性强的机制，用于定义与类相关的覆盖模型。例如：

在定义如下的类 xyz 中，成员 m_x 和 m_y 使用嵌入的覆盖组进行覆盖：
```verilog
class xyz;
    bit [3:0] m_x;
    int m_y;
    bit m_z;
    covergroup cov1 @m_z; // 嵌入的覆盖组
        coverpoint m_x;
        coverpoint m_y;
    endgroup
    function new(); cov1 = new; endfunction
endclass
```

在这个示例中，类 xyz 的数据成员 m_x 和 m_y 在每次数据成员 m_z 改变时被采样。

类中的覆盖组声明是一个 *嵌入的覆盖组* 声明。嵌入的覆盖组声明声明了一个匿名覆盖组类型和一个匿名类型的实例变量。covergroup_identifier 定义了实例变量的名称。在上面的示例中，隐式声明了一个变量 cov1（匿名覆盖组）。

嵌入的覆盖组可以定义类的保护和局部属性的覆盖模型，而不需要对类数据封装进行任何更改。类成员可以在覆盖点表达式中使用，也可以在其他覆盖构造中使用，如条件保护或选项初始化。

一个类可以有多个覆盖组。下面的示例展示了类 MC 中的两个覆盖组：
```verilog
class MC;
    logic [3:0] m_x;
    local logic m_z;
    bit m_e;
    covergroup cv1 @(posedge clk); coverpoint m_x; endgroup
    covergroup cv2 @m_e ; coverpoint m_z; endgroup
endclass
```

在覆盖组 cv1 中，公共类成员变量 m_x 在信号 clk 的每个上升沿上采样。局部类成员 m_z 由另一个覆盖组 cv2 进行覆盖。每个覆盖组由不同的时钟事件采样。

嵌入的覆盖组变量只能在 new 方法中赋值。嵌入的覆盖组可以在 new 方法中显式实例化。如果没有，则不会创建覆盖组，也不会对数据进行采样。

以下是一个嵌入的覆盖组的示例，它没有传入参数，并使用显式实例化与另一个对象同步：
```verilog
class Helper;
    int m_ev;
endclass

class MyClass;
    Helper m_obj;
    int m_a;
    covergroup Cov @(m_obj.m_ev);
        coverpoint m_a;
    endgroup

    function new();
        m_obj = new;
        Cov = new; // 在创建 m_obj 后创建嵌入的覆盖组
    endfunction
endclass
```

在这个示例中，覆盖组 Cov 嵌入在 MyClass 类中，该类包含一个 Helper 类型的对象 m_obj。嵌入覆盖组的时钟事件引用 m_obj 的数据成员 m_ev。因为覆盖组 Cov 使用 m_obj，所以必须在 Cov 之前实例化 m_obj。因此，在类构造函数中实例化 m_obj 的时候实例化嵌入的覆盖组 Cov。如上所示，嵌入覆盖组的实例化是通过将 new 操作符的结果赋值给覆盖组标识符来完成的。

下面的示例显示了如何使用传递给嵌入覆盖组的参数来设置覆盖组的覆盖选项：
```verilog
class C1;
    bit [7:0] x;

    covergroup cv (int arg) @(posedge clk);
        option.at_least = arg;
        coverpoint x;
    endgroup

    function new(int p1);
        cv = new(p1);
    endfunction
endclass

initial begin
    C1 obj = new(4);
end
```

## 19.5 定义覆盖点
覆盖组可以包含一个或多个覆盖点。覆盖点指定要覆盖的整数表达式。每个覆盖点包括与一些其采样值或其值转换相关联的箱。箱可以由用户显式定义，也可以由 SystemVerilog 自动创建。指定覆盖点的语法如下 19-2。覆盖点表达式（及其启用的 iff 条件，如果有的话）在覆盖组被采样时进行评估。表达式应在过程上下文中进行评估，因此表达式应合法地通过虚拟接口进行访问（见 25.9）。
---
```verilog
cover_point ::= // from A.2.11
[ [ data_type_or_implicit ] cover_point_identifier : ] coverpoint expression [ iff ( expression ) ] 
bins_or_empty 
bins_or_empty ::= 
{ {attribute_instance} { bins_or_options ; } }
| ;
bins_or_options ::= 
coverage_option 
| [ wildcard ] bins_keyword bin_identifier [ [ [ covergroup_expression ] ] ] =
{ covergroup_range_list } [ with ( with_covergroup_expression ) ] 
[ iff ( expression ) ] 
| [ wildcard ] bins_keyword bin_identifier [ [ [ covergroup_expression ] ] ] =
cover_point_identifier with ( with_covergroup_expression ) ] [ iff ( expression ) ] 
| [ wildcard ] bins_keyword bin_identifier [ [ [ covergroup_expression ] ] ] =
set_covergroup_expression [ iff ( expression ) ] 
| [ wildcard] bins_keyword bin_identifier [ [ ] ] = trans_list [ iff ( expression ) ] 
| bins_keyword bin_identifier [ [ [ covergroup_expression ] ] ] = default [ iff ( expression ) ] 
| bins_keyword bin_identifier = default sequence [ iff ( expression ) ] 
bins_keyword::= bins | illegal_bins | ignore_bins
covergroup_range_list ::= covergroup_value_range { , covergroup_value_range } 
covergroup_value_range ::= 
covergroup_expression 
| [ covergroup_expression : covergroup_expression ]25
with_covergroup_expression ::= covergroup_expression26
set_covergroup_expression ::= covergroup_expression27
covergroup_expression ::= expression28
// 25) 在形式为 [ expression : $ ] 或 [$: expression ] 的 open_value_range 或 covergroup_value_range 中使用 $ primary 是合法的。
// 26) 此表达式的结果应与整数类型兼容。
// 27) 此表达式受到 19.5.1.2 中描述的限制。
// 28) 此表达式受到 19.5 中描述的限制。
```
---
语法 19-2—覆盖点语法（摘自附录 A）

`coverpoint` 覆盖点创建了一个层次作用域，并可以选择标记。如果指定了标签，则它指定覆盖点的名称。此名称可用于将此覆盖点添加到交叉覆盖规范中或访问覆盖点的方法。如果省略标签并且覆盖点与单个变量相关联，则变量名成为覆盖点的名称。否则，实现可以仅为覆盖点生成一个名称，仅用于覆盖率报告，即生成的名称不能在语言内部使用。

在 data_type_or_implicit 中，`coverpoint` 可以显式或隐式指定数据类型。在任一情况下，应理解为为覆盖点指定了数据类型。数据类型应为整数类型。如果指定了数据类型，则还应指定 `cover_point_identifier`。

如果指定了数据类型，则覆盖点表达式应与数据类型赋值兼容。覆盖点的值应为指定的数据类型，并且应当像将覆盖点表达式分配给指定数据类型的变量一样确定。

如果没有指定数据类型，则覆盖点的推断数据类型应为覆盖点表达式的自决定类型。

覆盖点名称的可见性有限。标识符只能在以下上下文中引用覆盖点：
 - 在 `cross` 声明的覆盖点列表中（见 19.6）
 - 在层次名称中，其中前缀指定覆盖组变量的名称。例如，cov1.cp.option.weight，其中 cov1 是覆盖组变量的名称，cp 是在覆盖组中声明的覆盖点的名称。
 - 在 :: 之后，左操作数的作用域解析运算符引用覆盖组。例如，covtype :: cp :: type_option.weight。

只有常量表达式（见 11.2.1）、全局和实例常量（对于嵌入式覆盖组，见 19.4 和 8.19）或覆盖组的非 ref 参数允许在 covergroup_expression 中用作变量。

从覆盖组表达式中引用的全局和实例常量应为包含类的成员。这些实例常量的初始化器应出现在类构造函数中对覆盖组构造函数调用之前。这些初始化器不应和覆盖组构造调用出现在任何循环语句（见 12.7）或 fork—join_none 语句的主体中（无论是之前还是之后）。

函数调用可能参与 covergroup_expression，但是有下列语义限制：
 - 函数不得包含 `output` 或非 `const ref` 参数（`const ref` 是允许的）。
 - 函数应为自动的（或不保留状态信息）且没有副作用。
 - 函数不得引用函数外部的非常量变量。
 - 系统函数调用限制为常量系统函数调用（见 11.2.1）。

例如：
```verilog
covergroup cg ( ref int x , ref int y, input int c);
    coverpoint x; // 创建覆盖点 "x"，覆盖形式 "x"
    x: coverpoint y; // 无效：覆盖点标签 "x" 已存在
    b: coverpoint y; // 创建覆盖点 "b"，覆盖形式 "y"
    cx: coverpoint x; // 创建覆盖点 "cx"，覆盖形式 "x"
    option.weight = c; // 将 "cg" 的权重设置为形式 "c" 的值
    bit [7:0] d: coverpoint y[31:24]; // 创建覆盖点 "d"，覆盖形式 "y" 的高 8 位
    e: coverpoint x {
        option.weight = 2; // 设置覆盖点 "e" 的权重
    }
    e.option.weight = 2; // 无效使用 "e"，也是语法错误
    cross x, y { // 创建隐式覆盖点 "y"，覆盖形式 "y"。然后创建覆盖点 "x" 和 "y" 的交叉
        option.weight = c; // 将交叉的权重设置为形式 "c" 的值
    }
    b: cross y, x; // 无效：覆盖点标签 "b" 已存在
endgroup
```

覆盖点可以通过指定时钟块信号来采样对应于特定调度区域（见第 4 章）的值。因此，指示时钟块信号的覆盖点将从时钟块提供的值中采样。如果时钟块指定了 `#1step` 的偏移量，则覆盖点将从 Preponed 区域采样信号值。如果时钟块指定了 `#0` 的偏移量，则覆盖点将从 Observed 区域采样信号值。

`iff` 结构中的表达式指定一个可选条件，该条件禁用该覆盖点。如果在采样点处 guard 表达式求值为 false，则忽略覆盖点。例如：
```verilog
covergroup g4;
    coverpoint s0 iff(!reset);
endgroup
```

在上面的示例中，只有当值 reset 为 false 时，覆盖点 s0 才被覆盖。

覆盖点箱将名称和计数与一组值或一系列值转换相关联。如果箱指定一组值，则每次覆盖点匹配该组值之一时，计数将递增。如果箱指定一系列值转换，则每次覆盖点匹配整个值转换序列时，计数将递增。

覆盖点的箱可以由 SystemVerilog 自动创建，也可以通过使用 `bins` 构造显式定义来命名每个箱。未显式定义箱时，SystemVerilog 会自动创建它们。可以使用 auto_bin_max 覆盖选项来控制自动创建的箱数。覆盖选项在 19.7 中描述。

`default` 规范定义了一个与定义的值箱无关的箱。默认箱捕获不在任何定义的箱内的覆盖点的值。但是，覆盖点的覆盖率计算不应考虑默认箱捕获的覆盖。默认箱也不包括在交叉覆盖中（见 19.6）。默认对于捕获未计划或无效值很有用。`default sequence` 形式可用于捕获不在任何定义的转换箱内的所有转换（或序列）（见 19.5.2）。默认序列规范不接受多个转换箱（即，不允许 [] 表示）。`default` 或 `default dequence` 箱规范不能显式忽略（见 19.5.5）。对于指定为 ignore_bins 的箱也指定 `default` 或 `default dequence` 是错误的。

### 19.5.1 指定值的箱
`bins` 构造允许为给定范围列表中的每个值创建一个单独的箱，或为整个值范围创建一个单独的箱。为了为每个值创建一个单独的箱（一个箱数组），方括号 `[]` 应跟随箱名称。为一组值创建固定数量的箱，可以在方括号内指定一个正整数表达式。箱名称和可选的方括号后面跟随一个 covergroup_range_list，该列表指定与箱相关联的值集。在 covergroup_value_range 的形式 `[ expression : $ ]` 或 `[ $ : expression ]` 中，使用 `$ primary` 是合法的。

如果指定了固定数量的箱，并且该数量小于指定的值数量，则可能的箱值在指定的箱中均匀分布。前 N 个指定的值分配给第一个箱，接下来的 N 个指定的值分配给下一个箱，依此类推。重复的值保留；因此，相同的值可以分配给多个箱。如果值的数量不能被箱的数量整除，则最后一个箱将包含剩余的项目。例如：
```verilog
bins fixed [4] = { [1:10], 1, 4, 7 };
```

13 个可能的值分布如下：`<1,2,3>, <4,5,6>, <7,8,9>, <10,1,4,7>`。如果箱的数量超过值的数量，则一些箱将为空。

在箱定义的末尾的 `iff` 结构提供了一个每箱的保护条件。如果在采样点处 guard 表达式求值为 false，则不会增加箱的计数。
```verilog
bit [9:0] v_a;

covergroup cg @(posedge clk);
    coverpoint v_a
    {
        bins a = { [0:63],65 };
        bins b[] = { [127:150],[148:191] }; // 注意重叠值
        bins c[] = { 200,201,202 };
        bins d = { [1000:$] };
        bins others[] = default;
    }
endgroup
```

在上面的示例中，第一个 `bins` 构造将箱 a 与变量 v_a 的值在 0 到 63 和值 65 相关联。第二个 `bins` 构造创建了一组 65 个箱 `b[127]、b[128]，...b[191]`。同样，第三个 `bins` 构造创建了 3 个箱：`c[200]`、`c[201]` 和 `c[202]`。第四个 `bins` 构造将箱 d 与值在 1000 到 1023 之间的值相关联（`$` 代表 v_a 的最大值）。不匹配箱 `a`、`b[]`、`c[]` 或 `d` 的每个值都添加到其自己的独特箱中。

可以通过将其特性作为参数传递给构造函数来编写通用覆盖组。例如：
```verilog
covergroup cg (ref int ra, input int low, int high) @(posedge clk);
    coverpoint ra // 通过引用传递的采样变量
    {
        bins good = { [low : high] };
        bins bad[] = default;
    }
endgroup

...
int va, vb;

cg c1 = new( va, 0, 50 ); // 覆盖变量 va 在范围 0 到 50
cg c2 = new( vb, 120, 600 ); // 覆盖变量 vb 在范围 120 到 600
```

这个示例定义了一个覆盖组 cg，其中指定了要采样的信号和覆盖箱的范围。稍后，创建了两个覆盖组实例；每个实例采样不同的信号并覆盖不同范围的值。

#### 19.5.1.1 使用 covergroup 表达式的覆盖点箱
`with` 子句指定 covergroup_range_list 中只有满足给定表达式（例如，对于表达式计算为真，见 12.4 的描述）的值才包含在箱中。在表达式中，名称 item 用于表示候选值。候选值与覆盖点的类型相同。

覆盖点的名字可以用来代替定义箱的 covergroup_range_list，以表示覆盖点的所有值。只允许使用包含定义的箱的覆盖点名称；不允许使用其他覆盖点名称。例如：
```verilog
a: coverpoint x
{
    bins mod3[] = {[0:255]} with (item % 3 == 0);
}
```

这个箱定义选择了 0 到 255 之间所有能被 3 整除的值。

```verilog
coverpoint b
{
    bins func[] = b with (myfunc(item));
}
```

注意使用覆盖点名称 b 来表示 with_covergroup_expression 将应用于覆盖点的所有值。

与包含 `with` 的数组操作方法一样，如果表达式具有副作用，则结果是不可预测的。

`with` 子句的行为就好像在构造覆盖组实例时对 covergroup_range_list 中的值应用表达式一样。默认情况下，with_covergroup_expression 应用于分配值给箱之前的 covergroup_range_list 中的值集。如果希望在 with_covergroup_expression 应用之前分配值，则可以使用 distribute_first 覆盖组选项（见 19.7.1）来实现此排序。应用 with_covergroup_expression 的结果应保留多个等效的箱项以及箱顺序。这些规则的目的是允许使用非仿真分析技术来计算箱（例如，形式符号分析）或缓存先前计算的结果。

#### 19.5.1.2 使用 covergroup 表达式的覆盖点箱集
set_covergroup_expression 语法允许指定生成一个数组的表达式，该数组定义了箱。任何元素类型与覆盖点类型兼容的数组都是允许的，但是不允许关联数组。在覆盖组中声明的标识符（例如覆盖点标识符和箱标识符）不可见。表达式在构造覆盖组实例时进行评估。



