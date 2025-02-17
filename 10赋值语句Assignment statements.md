# 10. 赋值语句
## 10.1 概述
本章描述了以下内容：
 - 连续赋值
 - 过程阻塞和非阻塞赋值
 - 过程连续赋值（assign, deassign, force, release）
 - 线网别名

## 10.2 总览
赋值是将值放入线网和变量的基本机制。有两种基本形式的赋值，如下：
 - *连续赋值*，将值分配给线网或变量
 - *过程赋值*，将值分配给变量

连续赋值以类似门驱动线网或变量的方式驱动线网或变量。右侧的表达式可以被认为是一个连续驱动线网或变量的组合电路。相比之下，过程赋值将值放入变量。赋值没有持续时间；相反，变量保持赋值的值，直到对该变量的下一个过程赋值。

还有两种额外的赋值形式，`assign`/`deassign` 和 `force`/`release`，称为 *过程连续赋值*，在 10.6 描述。

赋值由两部分组成，左侧和右侧，由等号（`=`）字符分隔；或者，在非阻塞过程赋值的情况下，由小于等于（`<=`）字符对分隔。右侧可以是任何计算为值的表达式。左侧指示要将右侧值分配给的线网或变量。左侧可以采用表 10-1 中给出的形式之一，具体取决于赋值是连续赋值还是过程赋值。

表 10-1—赋值语句中的合法左侧形式
| 语句类型 | 左侧 |
| --- | --- |
| 连续赋值 | 线网或变量（向量或标量）<br> 线网或打包变量的常量位选择<br> 线网或打包变量的常量部分选择<br> 任何上述左侧的串联或嵌套串联 |
| 过程赋值 | 变量（向量或标量）<br> 打包变量的位选择<br> 打包变量的部分选择<br> 内存字<br> 数组<br> 数组元素选择<br> 数组切片<br> 任何上述左侧的串联或嵌套串联 |

SystemVerilog 还允许在赋值语句中指定时间单位，如下所示：
```verilog
#1ns r = a;
r = #1ns a;
r <= #1ns a;
assign #2.5ns sum = a + b;
```

## 10.3 连续赋值
连续赋值将值驱动到线网或变量，无论是向量（打包）还是标量。每当右侧的值发生变化时，就会发生这种赋值。连续赋值提供了一种模拟组合逻辑的方法，而无需指定门的互连。相反，模型指定了驱动线网或变量的逻辑表达式。

连续赋值有两种形式：*线网声明赋值*（见 10.3.1）和 *连续赋值语句*（见 10.3.2）。

连续赋值的语法如 10-1 所示。
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
list_of_net_decl_assignments ::= net_decl_assignment { , net_decl_assignment } // from A.2.3
net_decl_assignment ::= net_identifier { unpacked_dimension } [ = expression ] // from A.2.4
continuous_assign ::= // from A.6.1
assign [ drive_strength ] [ delay3 ] list_of_net_assignments ;
| assign [ delay_control ] list_of_variable_assignments ;
list_of_net_assignments ::= net_assignment { , net_assignment } 
list_of_variable_assignments ::= variable_assignment { , variable_assignment } 
net_assignment ::= net_lvalue = expression 
// 12) 电荷强度只能与 trireg 关键字一起使用。当使用 vectored 或 scalared 关键字时，至少应有一个打包维度。
```
---
语法 10-1—连续赋值的语法（摘自附录 A）

### 10.3.1 线网声明赋值
*线网声明赋值* 允许在声明线网的同一语句中将连续赋值放在线网上。

以下是线网声明形式的连续赋值的示例：
```verilog
wire (strong1, pull0) mynet = enable;
```

因为线网只能声明一次，所以对于特定线网只能进行一次线网声明赋值。这与连续赋值语句形成对比；一个线网可以接收多个连续赋值的形式。

*interconnect*（见 6.6.8）不得具有线网声明赋值。

### 10.3.2 连续赋值语句
连续赋值语句将连续赋值放在线网或变量数据类型上。线网可以显式声明，也可以根据 6.10 中定义的隐式声明规则继承隐式声明。变量必须在连续赋值语句之前显式声明。

对线网或变量的赋值应该是连续的和自动的。换句话说，每当右侧表达式中的操作数发生变化时，整个右侧表达式都应该被计算。如果新值与之前的值不同，则新值应该分配给左侧。

线网可以由多个连续赋值或由原语输出、模块输出和连续赋值的混合驱动。变量只能由一个连续赋值或一个原语输出或模块输出驱动。对于由连续赋值或输出驱动的变量，在声明或任何过程赋值中有初始化器是错误的。参见 6.5。

对于原子线网的连续赋值不应该驱动线网的一部分；整个 `nettype` 值应该被驱动。因此，对用户定义 `nettype` 的线网的连续赋值的左侧不应该包含任何索引或选择操作。

例1：以下是一个连续赋值的示例，该连续赋值已经被声明：
```verilog
wire mynet ;
assign (strong1, pull0) mynet = enable;
```

例2：以下是一个使用连续赋值建模带进位的 4 位加法器的示例。该赋值不能直接在线网的声明中指定，因为它需要在左侧进行串联。
```verilog
module adder (sum_out, carry_out, carry_in, ina, inb);
    output [3:0] sum_out;
    output carry_out;
    input [3:0] ina, inb;
    input carry_in;

    wire carry_out, carry_in;
    wire [3:0] sum_out, ina, inb;

    assign {carry_out, sum_out} = ina + inb + carry_in;
endmodule
```

例3：以下示例描述了一个具有一个 16 位输出总线的模块。它在四个输入总线中选择一个，并将所选总线连接到输出总线。
```verilog
module select_bus(busout, bus0, bus1, bus2, bus3, enable, s);
    parameter n = 16;
    parameter Zee = 16'bz;
    output [1:n] busout;
    input [1:n] bus0, bus1, bus2, bus3;
    input enable;
    input [1:2] s;

    tri [1:n] data; // 线网声明

    // 线网声明连续赋值
    tri [1:n] busout = enable ? data : Zee;

    // 四个连续赋值的赋值语句
    assign
        data = (s == 0) ? bus0 : Zee,
        data = (s == 1) ? bus1 : Zee,
        data = (s == 2) ? bus2 : Zee,
        data = (s == 3) ? bus3 : Zee;
endmodule
```

在模拟此示例时，将经历以下事件序列：
 - `a)` 检查总线选择器输入变量 s 的值。根据 s 的值，data 从四个输入总线中的一个接收。
 - `b)` data 的设置触发了 busout 的连续赋值。如果 enable 被设置，data 的内容将被分配给 busout；如果 enable 为 0，Zee 的内容将被分配给 busout。

### 10.3.3 连续赋值延迟
给连续赋值指定的延迟应该指定右侧操作数值变化到赋值到左侧的时间间隔。如果左侧引用标量线网，则延迟应该与门延迟一样处理；也就是说，可以为输出上升、下降和变为高阻态分别指定不同的延迟（见 28.16）。

如果左侧引用向量线网，则可以应用最多三个延迟。以下规则确定哪个延迟控制分配：
 - 如果右侧从非零到零进行转换，则应使用下降延迟。
 - 如果右侧进行转换为 z，则应使用关闭延迟。
 - 对于所有其他情况，应使用上升延迟。

如果左侧引用用户定义的 `nettype` 线网或该类线网的数组，则只能应用单个延迟。当对线网的值进行任何更改时，将使用指定的延迟。

指定连续赋值的延迟作为线网声明的一部分，应与指定线网延迟然后对线网进行连续赋值不同对待。在线网声明中，可以将延迟值应用于线网，如下例所示：
```verilog
wire #10 wireA;
```

这种语法称为 *线网延迟*，意味着任何其他语句应用到 wireA 的值变化都将延迟十个时间单位，然后才会生效。当声明中包含连续赋值时，延迟是连续赋值的一部分，不是线网延迟。因此，它不应添加到线网上的其他驱动器的延迟中。此外，如果赋值是向量线网，则如果在声明中包含赋值，则不应将上升和下降延迟应用于单个位。

右侧操作数发生变化在先前的变化尚未传播到左侧之前，则将采取以下步骤：
 - 计算右侧表达式的值。
 - 如果此右侧值与当前计划传播到左侧的值不同，则取消当前调度的传播事件。
 - 如果新的右侧值等于当前左侧值，则不会调度事件。
 - 如果新的右侧值与当前左侧值不同，则将按照标准方式使用左侧当前值、右侧新计算值和语句中指示的延迟计算延迟；然后调度一个新的传播事件，该事件将在延迟时间单位后发生。

### 10.3.4 连续赋值强度
连续赋值的驱动强度可以由用户指定。这仅适用于标量线网，除了类型为 `supply0` 和 `supply1` 的线网。

连续赋值驱动强度可以在线网声明中或在独立赋值中使用 `assign` 关键字指定。如果提供了强度规范，则应立即跟随关键字（线网类型的关键字或 assign）并在指定的延迟之前。每当连续赋值驱动线网时，值的强度应模拟为指定的强度。

驱动强度规范应包含一个强度值，当分配给线网的值为 1 时应用，另一个强度值，当分配值为 0 时应用。以下关键字应指定分配值为 1 时的强度值：
`supply1 strong1 pull1 weak1 highz1`

以下关键字应指定分配值为 0 时的强度值：
`supply0 strong0 pull0 weak0 highz0`

两个强度规范的顺序是任意的。以下两个规则约束了驱动强度规范的使用：
 - 强度规范 `(highz1, highz0)` 和 `(highz0, highz1)` 应被视为非法构造。
 - 如果未指定驱动强度，则默认为 `(strong1, strong0)`。

## 10.4 过程赋值
过程赋值发生在过程中，如 always、initial（见 9.2）、task 和 function（见第 13 章）中，并且可以被认为是“触发”赋值。当仿真中的执行流达到过程中的赋值时，触发发生。到达赋值可以由条件语句控制。事件控制、延迟控制、if 语句、case 语句和循环语句都可以用来控制是否计算赋值。第 12 章给出了详细的例子。

过程赋值的右侧可以是计算为值的任何表达式，但左侧的变量类型可能会限制右侧的合法表达式。左侧应该是一个变量，接收右侧的赋值。过程赋值的左侧可以采用以下形式之一：
 - 单变量，如第 6.4 节所述
 - 聚合变量，如第 7 章所述
 - 打包数组的位选择、部分选择和切片
 - 非打包数组的切片

SystemVerilog 包含以下三种过程赋值语句：
 - 阻塞过程赋值语句（见 10.4.1）
 - 非阻塞过程赋值语句（见 10.4.2）
 - 赋值运算符（见 11.4.1）

阻塞和非阻塞过程赋值语句在顺序块中指定不同的过程流。

### 10.4.1 阻塞过程赋值
*阻塞过程赋值* 语句应在顺序块（见 9.3.1）中的其后语句执行之前执行。阻塞过程赋值语句不应阻止并行块（见 9.3.2）中其后语句的执行。

阻塞过程赋值的语法如 10-2 所示。
---
```verilog
blocking_assignment ::= // from A.6.3
variable_lvalue = delay_or_event_control expression 
| nonrange_variable_lvalue = dynamic_array_new 
| [ implicit_class_handle . | class_scope | package_scope ] hierarchical_variable_identifier 
select = class_new 
| operator_assignment 
operator_assignment ::= variable_lvalue assignment_operator expression 
assignment_operator ::= 
= | += | -= | *= | /= | %= | &= | |= | ^= | <<= | >>= | <<<= | >>>=
```
---
语法 10-2—阻塞赋值语法（摘自附录 A）

在此语法中，*variable_lvalue* 是适用于过程赋值语句的数据类型，`=` 是赋值运算符，*delay_or_event_control* 是可选的赋值内控制（见 9.4.5）。expression 是要分配给左侧的右侧值。如果 *variable_lvalue* 需要计算，则应在赋值语句指定的时间进行计算。如果未指定时间控制，则 variable_lvalue 和右侧表达式的计算顺序是未定义的。参见 4.9.3。

阻塞过程赋值使用的 `=` 赋值运算符也被过程连续赋值和连续赋值使用。

以下示例显示了阻塞过程赋值：
```verilog
rega = 0;
rega[3] = 1; // 位选择
rega[3:5] = 7; // 部分选择
mema[address] = 8'hff; // 分配给 mem 元素
{carry, acc} = rega + regb; // 串联
```

附加赋值运算符，如 `+=`，在 11.4.1 中描述。

### 10.4.2 非阻塞过程赋值
*非阻塞过程赋值* 允许在不阻止过程流的情况下进行赋值调度。非阻塞过程赋值语句可以在同一时间步骤内进行多个变量赋值，而不考虑顺序或相互依赖。

把非阻塞过程赋值语句用于自动变量是非法的。

非阻塞过程赋值的语法如 10-3 所示。
---
```verilog
nonblocking_assignment ::= variable_lvalue <= [ delay_or_event_control ] expression // from A.6.3
```
---
语法 10-3—非阻塞赋值语法（摘自附录 A）

在此语法中，*variable_lvalue* 是适用于过程赋值语句的数据类型，`<=` 是非阻塞赋值运算符，*delay_or_event_control* 是可选的赋值内控制（见 9.4.5）。如果 *variable_lvalue* 需要计算，例如索引表达式、类句柄或虚拟接口引用，则应在右侧表达式的同时计算。variable_lvalue 和右侧表达式的计算顺序是未定义的（见 4.9.4）。

非阻塞赋值运算符和小于等于关系运算符一样。应根据出现的上下文决定解释。当在表达式中使用 `<=` 时，应将其解释为关系运算符；当在非阻塞过程赋值中使用时，应将其解释为赋值运算符。

非阻塞过程赋值应在两个步骤中进行评估，如第 4 章所述。这两个步骤如下面的示例所示：

例1：
```verilog
module evaluates (out);
    output out;
    logic a, b, c;

    initial begin
        a = 0;
        b = 1;
        c = 0;
    end

    always c = #5 ~c;

    always @(posedge c) begin
        a <= b; // 两步中评估、计算和执行
        b <= a;
    end
endmodule
```

步骤 1：
在 posedge c 时，仿真器计算非阻塞赋值的右侧，并在 *非阻塞赋值更新* 事件的 NBA 区域末尾调度新值的赋值。非阻塞赋值调度在时刻 5 改变 `a = 0`； `b = 1`。

步骤 2：
当仿真器激活非阻塞赋值更新事件时，它更新每个非阻塞赋值语句的左侧。赋值值 `a = 1`；`b = 0`。

*在时间步骤结束* 意味着非阻塞赋值是时间步骤中执行的最后一个赋值，除了一个例外。非阻塞赋值事件可以创建阻塞赋值事件。这些阻塞赋值事件将在计划的非阻塞事件之后处理。

不像用于阻塞赋值的事件或延迟控制，非阻塞赋值不会阻止过程流。非阻塞赋值计算和调度赋值，但不会阻止 begin-end 块中后续语句的执行。

例2：
```verilog
module nonblock1;
    logic a, b, c, d, e, f;

    // 阻塞赋值
    initial begin
        a = #10 1; // a 将在时间 10 被赋值为 1
        b = #2 0; // b 将在时间 12 被赋值为 0
        c = #4 1; // c 将在时间 16 被赋值为 1
    end

    // 非阻塞赋值
    initial begin
        d <= #10 1; // d 将在时间 10 被赋值为 1
        e <= #2 0; // e 将在时间 2 被赋值为 0
        f <= #4 1; // f 将在时间 4 被赋值为 1
    end
endmodule
```

如前面的示例所示，仿真器计算并调度当前时间步骤结束的赋值，并可以执行与非阻塞过程赋值的交换操作。

例3：
```verilog
module nonblock2;
    logic a, b;

    initial begin
        a = 0;
        b = 1;
        a <= b; // 两步中计算、调度和执行
        b <= a;
    end

    initial begin
        $monitor ($time, ,"a = %b b = %b", a, b); // a = 1, b = 0
        #100 $finish;
    end
endmodule
```

步骤 1：仿真器计算非阻塞赋值的右侧，并调度当前时间步骤结束时的非阻塞赋值的左侧更新。

步骤 2：在当前时间步骤结束时，仿真器更新每个非阻塞赋值语句的左侧。

对于给定变量的不同非阻塞赋值的执行顺序应该保持不变。换句话说，如果存在一组非阻塞赋值的执行顺序，则结果更新的目的地的顺序应与执行的顺序相同（见 4.6）。

例4：
```verilog
module multiple;
    logic a;

    initial a = 1;
    // 变量的赋值是确定的
    initial begin
        a <= #4 0; // 在时间 4 时调度 a = 0
        a <= #4 1; // 在时间 4 时调度 a = 1
    end // 在时间 4 时，a = 1
endmodule
```

如果仿真器同时执行两个过程块，并且这两个过程块包含对同一变量的非阻塞赋值运算符，则该变量的最终值是不确定的。例如，变量 a 的值在以下示例中是不确定的：

例5：
```verilog
module multiple2;
    logic a;

    initial a = 1;
    initial a <= #4 0; // 在时间 4 时调度 0
    initial a <= #4 1; // 在时间 4 时调度 1
    // 在时间 4 时，a = ??
    // 变量的赋值是不确定的
endmodule
```

两个非阻塞赋值目标是同一变量的事实并不足以使对变量的赋值的顺序不确定。例如，变量 a 在以下示例中的时间周期 16 结束时的值是确定的：

例6：
```verilog
module multiple3;
    logic a;

    initial #8 a <= #8 1; // 在时间 8 时执行；在时间 16 时调度 a = 1
    initial #12 a <= #4 0; // 在时间 12 时执行；在时间 16 时调度 a = 0
    // 因为确定了将 a 更新为值 1 的更新在将 a 更新为值 0 的更新之前调度，
    // 所以确定 a 在时间步 16 结束时的值为 0
endmodule
```

以下示例显示了如何将 `i[0]` 的值分配给 r1，以及如何在每个时间延迟后调度赋值：

例7：
```verilog
module multiple4;
    logic r1;
    logic [2:0] i;

    initial begin
        // 在不取消之前赋值的情况下对 r1 进行赋值
        for (i = 0; i <= 5; i++)
            r1 <= # (i*10) i[0]; // 每隔 10 个时间单位翻转 r1
    end
endmodule
```

## 10.5 变量声明赋值（变量初始化）
与线网不同，变量不能在其声明的一部分具有隐式连续赋值。作为变量声明的一部分的赋值是变量初始化，而不是连续赋值。

变量声明赋值是过程赋值的一种特殊情况，它将值放入变量。它允许在声明变量的同一语句中放置初始值（见 6.8）。赋值没有持续时间；相反，变量保持赋值的值，直到对该变量的下一个赋值。

例如：
```verilog
wire w = vara & varb; // 具有连续赋值的线网
logic v = consta & constb; // 具有初始化的变量
```

在开始任何初始或始终过程之前，应在变量声明的一部分（包括静态类成员）设置静态变量的初始值。另见 6.21。

## 10.6 过程连续赋值
*过程连续赋值*（使用关键字 `assign` 和 `force`）是允许将表达式连续驱动到变量或线网的过程语句。这些语句的语法如 10-4 所示。
---
```verilog
procedural_continuous_assignment ::= // from A.6.2
assign variable_assignment 
| deassign variable_lvalue 
| force variable_assignment 
| force net_assignment 
| release variable_lvalue 
| release net_lvalue 
variable_assignment ::= variable_lvalue = expression 
net_assignment ::= net_lvalue = expression // from A.6.1
```
---
语法 10-4—过程连续赋值的语法（摘自附录 A）

assign 过程连续赋值语句或 force 语句的右侧可以是一个表达式。这应该被视为连续赋值；也就是说，如果右侧的任何变量发生变化，则在 assign 或 force 生效时将重新计算赋值。例如：
```verilog
force a = b + f(c) ;
```

在这里，如果 b 或 c 发生变化，a 将被强制为 b+f(c) 的新值。

### 10.6.1 assign 和 deassign 过程语句
`assign` 过程连续赋值语句应覆盖对变量的所有过程赋值。`deassign` 过程语句应结束对变量的过程连续赋值。变量的值应保持不变，直到通过过程赋值或过程连续赋值对变量进行新值分配。assign 和 deassign 过程语句允许，例如，对 D 类边沿触发器上的异步清除/预置进行建模，其中在清除或预置处于活动状态时抑制时钟。

*assign 语句* 中赋值的左侧应是一个单一变量引用或变量的连接。它不应是变量的位选择或部分选择。

如果对已经有过程连续赋值的变量应用关键字 assign，则此新的过程连续赋值应在进行新的过程连续赋值之前对变量进行 deassign。

以下示例显示了在 D 类触发器的行为描述中使用 assign 和 deassign 过程语句的用法：
```verilog
module dff (q, d, clear, preset, clock);
    output q;
    input d, clear, preset, clock;
    logic q;
    always @(clear or preset)
        if (!clear)
            assign q = 0;
        else if (!preset)
            assign q = 1;
        else
            deassign q;
    always @(posedge clock)
        q = d;
endmodule
```

如果 clear 或 preset 低，则输出 q 将持续保持适当的常量值，并且时钟上的正边沿不会影响 q。当清除和预置都高时，q 被 deassign。

注意：过程 assign 和 deassign 结构正在考虑弃用。请参见附录 C。

### 10.6.2 force 和 release 过程语句
另一种形式的过程连续赋值是 `force` 和 `release` 过程语句。这些语句具有与 `assign-deassign` 相似的效果，但 force 可以应用于线网以及变量。赋值的左侧可以是对单一变量、线网、向量线网的常量位选择、向量线网的常量部分选择或这些的连接的引用。它不应是变量或具有用户定义 nettype 的线网的位选择或部分选择。force 或 release 语句不应应用于通过连续和过程赋值的混合进行赋值的变量。

对变量的 force 语句应覆盖对变量的过程赋值、连续赋值或 assign 过程连续赋值，直到对变量执行 release 过程语句。释放后，如果变量没有被连续赋值驱动，并且当前没有活动的 assign 过程连续赋值，则变量不会立即更改值，并且将保持其当前值，直到对变量的下一个过程赋值执行。释放由连续赋值驱动的变量或当前具有活动的 assign 过程连续赋值，则将重新建立该赋值，并在连续赋值的调度区域中调度重新计算。

对线网的 `force` 过程语句应覆盖线网的所有驱动器——门输出、模块输出和连续赋值，直到执行线网的 release 过程语句。释放后，线网应立即被赋予由线网的驱动器确定的值。

例如：
```verilog
module test;
    logic a, b, c, d;
    wire e;

    and and1 (e, a, b, c);

    initial begin
        $monitor("%d d=%b,e=%b", $stime, d, e);
        assign d = a & b & c;
        a = 1;
        b = 0;
        c = 1;
        #10;
        force d = (a | b | c);
        force e = (a | b | c);
        #10;
        release d;
        release e;
        #10 $finish;
    end
endmodule

结果：
 0 d=0,e=0
10 d=1,e=1
20 d=0,e=0
```

在此示例中，一个 `and` 门实例 and1 通过 force 过程语句“修补”为一个 or 门，将其输出强制为其输入的 OR 值，并且一个 AND 值的 assign 过程语句“修补”为一个 OR 值的 assign 语句。

## 10.7 赋值扩展和截断
赋值的左侧的大小形成右侧表达式的上下文。

以下是计算赋值的步骤：
 - 通过标准表达式大小确定规则（见 11.8.1）确定左侧和右侧的大小。
 - 当右侧表达式的位数少于左侧时，将右侧值填充到左侧的大小。如果右侧是无符号的，则根据 11.6.1 中指定的规则进行填充。如果右侧是有符号的，则进行符号扩展。
 - 如果左侧小于右侧，则应发生截断，如下面的段落所述。

如果赋值的右侧表达式的宽度大于赋值的左侧的宽度，则应丢弃右侧表达式的 MSB 以匹配左侧的大小。实现可以但不需要警告或报告与赋值大小不匹配或截断相关的任何错误。大小转换可以用于指示显式更改大小的明确意图（见 6.24.1）。截断有符号表达式的符号位可能会更改结果的符号。

以下是赋值截断的一些示例。

例1：
```verilog
logic [5:0] a;
logic signed [4:0] b;

initial begin
    a = 8'hff; // 赋值后，a = 6'h3f
    b = 8'hff; // 赋值后，b = 5'h1f
end
```

例2：
```verilog
logic [0:5] a;
logic signed [0:4] b, c;

initial begin
    a = 8'sh8f; // 赋值后，a = 6'h0f
    b = 8'sh8f; // 赋值后，b = 5'h0f
    c = -113; // 赋值后，c = 15
    // 1000_1111 = (-'h71 = -113) 截断为 ('h0F = 15)
end
```

例3：
```verilog
logic [7:0] a;
logic signed [7:0] b;
logic signed [5:0] c, d;

initial begin
    a = 8'hff;
    c = a; // 赋值后，c = 6'h3f
    b = -113;
    d = b; // 赋值后，d = 6'h0f
end
```

## 10.8 类似赋值的上下文
类似赋值的上下文如下：
 - 连续或过程赋值
 - 对具有显式类型声明的参数的赋值：
   - 模块、接口、程序或类中的参数值赋值
   - 模块、接口或程序的实例化中的参数值覆盖
   - 类的实例化或类作用域运算符的左侧中的参数值覆盖
 - 用于子例程输入、输出或 inout 端口的值传递
 - 函数中的返回语句
 - 标记联合表达式
 - 用作赋值类似上下文中右侧值的表达式：
   - 如果是括号表达式，则是括号内的表达式
   - 如果是 mintypmax 表达式，则是冒号分隔的表达式
   - 如果是条件运算符表达式，则是第二个和第三个操作数
 - 赋值模式中的表达式与数据对象或数据值中的字段或元素之间的非默认对应

不应将其他上下文视为类似赋值的上下文。特别地，不应将以下上下文视为类似赋值的上下文：
 - 静态转换
 - 赋值模式中的表达式和数据对象或数据值中的字段或元素之间的默认对应
 - 模块、接口或程序声明中的端口表达式
 - 传递给子例程 ref 端口的值
 - 将值传递给模块、接口或程序的 inout 或 ref 端口

## 10.9 赋值模式
赋值模式用于赋值，用于描述对结构字段和数组元素的赋值的模式。

赋值模式指定表达式集合和数据对象或数据值中的字段和元素之间的对应关系。赋值模式没有自我确定的数据类型，但可以在赋值类似上下文中的一侧使用（见 10.8），当另一侧具有自我确定的数据类型时。赋值模式由大括号、键和表达式构建，并以撇号为前缀。例如：
```verilog
var int A[N] = '{default:1};
var integer i = '{31:1, 23:1, 15:1, 8:1, default:0};

typedef struct {real r, th;} C;
var C x = '{th:PI/2.0, r:1.0};
var real y [0:1] = '{0.0, 1.1}, z [0:9] = '{default: 3.1416};
```

也可以使用不带键的位置表示法。例如：
```verilog
var int B[4] = '{a, b, c, d};
var C y = '{1.0, PI/2.0};
'{a, b, c, d} = B;
```

当赋值模式用作类似赋值上下文中的左侧时，应要求位置表示法；每个成员表达式应具有与右侧对应元素的数据类型赋值兼容并具有相同位数的比特流数据类型。

赋值模式的语法列在语法 10-5 中。
---
```verilog
assignment_pattern ::= // from A.6.7.1
'{ expression { , expression } }
| '{ structure_pattern_key : expression { , structure_pattern_key : expression } }
| '{ array_pattern_key : expression { , array_pattern_key : expression } }
| '{ constant_expression { expression { , expression } } }
structure_pattern_key ::= member_identifier | assignment_pattern_key 
array_pattern_key ::= constant_expression | assignment_pattern_key 
assignment_pattern_key ::= simple_type | default
assignment_pattern_expression ::= 
[ assignment_pattern_expression_type ] assignment_pattern 
assignment_pattern_expression_type ::= 
ps_type_identifier 
| ps_parameter_identifier
| integer_atom_type 
| type_reference 
constant_assignment_pattern_expression32 ::= assignment_pattern_expression 
// 32) 在常量_assignment_pattern_expression 中，所有成员表达式应为常量表达式。
```
---
语法 10-5—赋值模式语法（摘自附录 A）

赋值模式可用于构造或解构结构或数组，方法是将数据类型名称作为模式前缀，形成赋值模式表达式。与赋值模式不同，赋值模式表达式具有自我确定的数据类型，并且不限于在赋值类似上下文中的一侧。当赋值模式表达式用于右侧表达式时，应产生变量的值，该变量的数据类型如果使用赋值模式进行初始化，则将保持该值。

```verilog
typedef logic [1:0] [3:0] T;
shortint'({T'{1,2}, T'{3,4}}) // 产生 16'sh1234
```

当赋值模式表达式用于左侧表达式时，应要求位置表示法；并且每个成员表达式应具有一个比特流数据类型，该类型与赋值模式表达式的数据类型中的对应元素具有相同的比特数。如果右边的表达式具有自确定的数据类型，那么它应该与赋值模式表达式的数据类型兼容并具有相同的位数。

```verilog
typedef byte U[3];
var U A = '{1, 2, 3};
var byte a, b, c;
U'{a, b, c} = A;
U'{c, a, b} = '{a+1, b+1, c+1};
```

赋值模式表达式不应用于模块、接口或程序声明中的端口表达式。

### 10.9.1 数组赋值模式
拼接大括号用于构造和解构简单位向量。类似的语法用于支持数组的构造和解构。表达式应该逐个元素匹配，大括号应该匹配数组维度。每个表达式项应在分配给数组元素的类型上下文中进行计算。换句话说，以下示例不需要引起大小警告：
```verilog
bit unpackedbits [1:0] = '{1,1}; // 不需要大小警告，因为 bit 可以设置为 1
int unpackedints [1:0] = '{1'b1, 1'b1}; // 不需要大小警告，因为 int 可以设置为 1'b1
```

类似于复制（见 11.4.12.1）的语法也可以用于数组赋值模式。每个复制应表示整个单个维度。
```verilog
unpackedbits = '{2 {y}} ; // 与 '{y, y} 相同
int n[1:2][1:3] = '{2{'{3{y}}}}; // 与 '{'{y,y,y},'{y,y,y}} 相同
```

SystemVerilog 在赋值上下文中使用大括号时确定上下文。

有时将数组元素设置为一个值是有用的，而不必跟踪成员的数量。这可以使用 `default` 关键字完成：
```verilog
initial unpackedints = '{default:2}; // 将元素设置为 2
```

对于结构数组，指定一个或多个匹配类型键是有用的，如下面的结构赋值模式所述。

```verilog
struct {int a; time b;} abkey[1:0];
abkey = '{'{a:1, b:2ns}, '{int:5, time:$time}};
```

匹配规则如下：
 - 索引：值 指定键元素索引的显式值。该值在分配给索引元素的上下文中进行计算，并且应该可以转换为其类型。在单个数组模式表达式中多次指定相同索引是错误的。
 - 类型：值 如果数组的元素或子数组类型与此类型匹配，则每个未由索引键上面设置的元素或子数组将设置为该值。该值应该可以转换为数组元素或子数组类型。否则，如果数组是多维的，则将递归地下降到数组的每个子数组中，使用本节中的规则和类型和默认键。否则，如果数组是结构数组，则将递归地下降到数组的每个元素中，使用结构赋值模式的规则和类型和默认键。如果多个类型匹配相同元素，则使用最后一个值。
 - 默认：值 应用于未由索引或类型键匹配的元素或子数组。如果元素或子数组的类型是简单位向量类型、与值的自我确定类型匹配，或者不是数组或结构类型，则该值在每次由默认键分配时在上下文中进行计算，并且应该可以转换为元素或子数组的类型。对于未匹配的子数组，类型和默认指定符根据本子句中的规则递归应用于其每个元素或子数组。对于未匹配的结构元素，根据结构的规则应用类型和默认键。

每个元素都应该由这些规则中的一个覆盖。

如果在具有副作用的表达式上使用类型键、默认键或复制运算符，则该表达式的计算次数是未定义的。

### 10.9.2 结构赋值模式
结构可以使用由成员表达式构建的结构赋值模式进行构造和解构。复制运算符可以用于设置确切数量的成员。每个成员表达式应在分配给结构成员的上下文中进行计算。也可以使用成员名称构建结构赋值模式。

```verilog
module mod1;
    typedef struct {
        int x;
        int y;
    } st;
    st s1;
    int k = 1;
    initial begin
        #1 s1 = '{1, 2+k}; // 按位置
        #1 $display( s1.x, s1.y);
        #1 s1 = '{x:2, y:3+k}; // 按名称
        #1 $display( s1.x, s1.y);
        #1 $finish;
    end
endmodule
```

有时将结构成员设置为一个值是有用的，而不必跟踪成员的数量。这可以使用 `default` 关键字完成：
```verilog
initial s1 = '{default:2}; // 将 x 和 y 设置为 2
```

`'{member:value}` 或 `'{data_type: default_value}` 语法也可以使用：
```verilog
ab abkey[1:0] = '{'{a:1, b:1.0}, '{int:2, shortreal:2.0}};
```

`default` 关键字的使用适用于嵌套结构的成员或结构中未打包数组的元素。

```verilog
struct {
    int A;
    struct {
        int B, C;
    } BC1, BC2;
} ABC, DEF;

ABC = '{A:1, BC1:'{B:2, C:3}, BC2:'{B:4,C:5}};
DEF = '{default:10};
```

为了解决不同类型的成员的问题，可以使用类型作为键。这将覆盖该类型的默认值：
```verilog
typedef struct {
    logic [7:0] a;
    bit b;
    bit signed [31:0] c; 
    string s;
} sa;

sa s2;
initial s2 = '{int:1, default:0, string:""}; // 将所有设置为 0，除了位数组设置为 1 和字符串设置为 ""
```

同样，可以设置单个成员以覆盖一般默认值和类型默认值：
```verilog
initial #10 s2 = '{default:'1, s : ""}; // 将所有设置为 1，除了 s 设置为 ""
```

SystemVerilog 在赋值上下文中使用大括号时确定上下文。

匹配规则如下：
 - 成员：值 指定结构的顶层成员的显式值。该值在分配给命名成员的上下文中进行计算，并且应该可以转换为成员类型。否则，将生成错误。
 - 类型：值 指定结构中每个字段的类型。如果字段的类型与此类型匹配，则将每个未由成员键上面设置的字段设置为该值。该值应该可以转换为字段类型。否则，如果字段是结构类型，则将递归地下降到结构的每个字段中，使用本节中的规则和类型和默认键。如果多个类型匹配相同字段，则使用最后一个值。
 - 默认：值 应用于未由成员或类型键匹配的字段。如果字段的类型是简单位向量类型、与值的自我确定类型匹配，或者不是数组或结构类型，则该值在每次由默认键分配时在上下文中进行计算，并且应该可以转换为字段类型。对于未匹配的结构字段，类型和默认指定符根据本子句中的规则递归应用于其每个字段。

每个成员都应该由这些规则中的一个覆盖。

如果在具有副作用的表达式上使用类型键、默认键或复制运算符，则该表达式的计算次数是未定义的。



