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


