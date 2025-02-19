# 13. 任务和函数（子程序）
## 13.1 概述
本章描述以下内容：
 - 任务声明
 - 函数声明
 - 调用任务和函数

## 13.2 总览
任务和函数提供了从描述的几个不同位置执行常见过程的能力。它们还提供了一种将大型过程分解为较小过程的方法，以便更容易阅读和调试源描述。本章讨论了任务和函数之间的区别，描述了如何定义和调用任务和函数，并提供了每个的示例。

任务和函数统称为 *子程序*。

以下规则区分了任务和函数，13.4.4 中有例外：
 - 函数体中的语句应在一个模拟时间单位内执行；任务可以包含时间控制语句。
 - 函数不能启用任务；任务可以启用其他任务和函数。
 - 非空函数应返回单个值；任务或空函数不应返回值。
 - 非空函数可以用作表达式的操作数；该操作数的值是函数返回的值。

例如：

任务或函数可以定义为交换 16 位字中的字节。任务将在输出参数中返回交换的字，因此启用名为 `switch_bytes` 的任务的源代码可能如下所示：

```verilog
switch_bytes (old_word, new_word);
```

`switch_bytes` 任务将获取 `old_word` 中的字节，颠倒它们的顺序，并将颠倒的字节放入 `new_word` 中。

字节交换函数将返回交换的字作为函数的返回值。因此，函数 `switch_bytes` 的函数调用可能如下所示：

```verilog
new_word = switch_bytes (old_word);
```

## 13.3 任务
任务应从定义传递参数值的语句启用，这些参数值将传递给任务和接收结果的变量。任务完成后，控制将返回到启用过程。因此，如果任务中有时间控制，则启用任务的时间可能与返回控制的时间不同。任务可以启用其他任务，这些任务又可以启用其他任务，而无论启用了多少任务，控制都不会返回，直到所有启用的任务都完成。

任务声明的语法如下 13-1：
---
```verilog
task_declaration ::= task [ lifetime ] task_body_declaration // from A.2.7
task_body_declaration ::= 
[ interface_identifier . | class_scope ] task_identifier ;
{ tf_item_declaration } 
{ statement_or_null } 
endtask [ : task_identifier ] 
| [ interface_identifier . | class_scope ] task_identifier ( [ tf_port_list ] ) ;
{ block_item_declaration } 
{ statement_or_null } 
endtask [ : task_identifier ] 
tf_item_declaration ::= 
block_item_declaration 
| tf_port_declaration 
tf_port_list ::= 
tf_port_item { , tf_port_item } 
tf_port_item23 ::= 
{ attribute_instance } 
[ tf_port_direction ] [ var ] data_type_or_implicit 
[ port_identifier { variable_dimension } [ = expression ] ] 
tf_port_direction ::= port_direction | const ref
tf_port_declaration ::= 
{ attribute_instance } tf_port_direction [ var ] data_type_or_implicit list_of_tf_variable_identifiers ;
lifetime ::= static | automatic // from A.2.1
signing ::= signed | unsigned // from A.2.2.1
data_type_or_implicit ::= 
data_type 
| implicit_data_type 
implicit_data_type ::= [ signing ] { packed_dimension } 
// 23) 在 tf_port_item 中，除了在 function_prototype 或 task_prototype 中，省略显式的 port_identifier 是非法的。
```
---
语法 13-1—任务语法（摘自附录 A）

任务声明具有形式参数，形式参数可以在括号中（类似于 ANSI C）或在声明和方向中指定。

```verilog
task mytask1 (output int x, input logic y);
    ...
endtask

task mytask2;
    output x;
    input y;
    int x;
    logic y;
    ...
endtask
```

每个形式参数具有以下方向之一：
 - `input` // 在开始时复制值
 - `output` // 在结束时复制值
 - `inout` // 在开始时复制值，在结束时复制值
 - `ref` // 传递引用（见 13.5.2）

如果未指定方向，则默认方向为 input。一旦给出方向，后续的形式参数默认为相同的方向。在下面的示例中，形式参数 a 和 b 默认为输入，u 和 v 都是输出：
    
```verilog
task mytask3(a, b, output logic [15:0] u, v);
    ...
endtask
```

每个形式参数都有一个数据类型，可以显式声明或从前一个参数继承。如果未显式声明数据类型，则默认数据类型为 `logic`，如果是第一个参数或参数方向明确指定。否则，数据类型从前一个参数继承。

可以将数组指定为任务的形式参数。例如：

```verilog
// b 的结果声明是 input [3:0][7:0] b[3:0]
task mytask4(input [3:0][7:0] a, b[3:0], output [3:0][7:0] y[1:0]);
    ...
endtask
```

任务声明和 `endtask` 之间可以写多个语句。语句按顺序执行，就像它们被包含在 `begin` .... `end` 组中一样。也可以完全没有语句。

`endtask` 到达时任务退出。`return` 语句可用于在 `endtask` 关键字之前退出任务。

对任务的调用也称为 *任务启用*（有关调用任务的更多详细信息，请参见 13.5）。

示例 1：以下示例说明了任务定义的基本结构，其中有五个参数：

```verilog
task my_task; 
    input a, b; 
    inout c; 
    output d, e;
    . . . // 执行任务工作的语句
    . . .
    c = a; // 初始化结果输出的赋值
    d = b;
    e = c;
endtask
```

或者使用任务声明的第二种形式，任务可以定义如下：

```verilog
task my_task (input a, b, inout c, output d, e); 
    . . . // 执行任务工作的语句
    . . .
    c = a; // 初始化结果变量的赋值
    d = b;
    e = c;
endtask
```

以下语句调用任务：

```verilog
initial
    my_task (v, w, x, y, z);
```

任务调用参数（v, w, x, y 和 z）对应于任务定义的参数（a, b, c, d 和 e）。在调用时，输入和 inout 类型参数（a, b 和 c）接收传递的值 v, w 和 x。因此，调用的执行实际上导致以下赋值：

```verilog
a = v;
b = w;
c = x;
```

作为任务处理的一部分，`my_task` 的任务定义将计算的结果值放入 c, d 和 e 中。任务完成后，执行以下赋值以将计算的值返回给调用过程：

```verilog
x = c;
y = d;
z = e;
```

示例 2：以下示例说明了任务的使用，描述了一个交通灯顺序器：

```verilog
module traffic_lights;
    logic clock, red, amber, green;
    parameter on = 1, off = 0, red_tics = 350, 
    amber_tics = 30, green_tics = 200;

    // 初始化颜色
    initial red = off;
    initial amber = off; 
    initial green = off;

    always begin // 控制灯的序列
        red = on; // 打开红灯
        light(red, red_tics); // 等待。
        green = on; // 打开绿灯
        light(green, green_tics); // 等待。
        amber = on; // 打开黄灯
        light(amber, amber_tics); // 等待。
    end

    // 等待 'tics' 个正边沿时钟后关闭 'color' 灯的任务
    task light (output color, input [31:0] tics); 
        repeat (tics) @ (posedge clock);
        color = off; // 关闭灯。
    endtask: light

    always begin // 时钟波形
        #100 clock = 0;
        #100 clock = 1;
    end
endmodule: traffic_lights
```

### 13.3.1 静态和自动任务
在模块、接口、程序或包中定义的任务默认为静态任务，所有声明的项都是静态分配的。这些项将在所有并发执行的任务之间共享。

任务可以定义为使用自动存储，使用以下两种方式：
 - 作为任务声明的一部分使用可选的 automatic 关键字显式声明。
 - 通过定义为自动的模块、接口、程序或包中定义任务隐式声明。

在类中定义的任务始终是自动的（见 8.6）。

自动任务中声明的所有项都将在每次调用时动态分配。所有形式参数和局部变量都存储在堆栈上。

自动任务项不能通过层次引用访问。自动任务可以通过其层次名称调用。

可以在静态任务中声明特定的局部变量为 `automatic`，也可以在自动任务中声明为 `static`。

### 13.3.2 任务内存使用和并发激活
任务可以同时启用多次。自动任务的所有变量将在每次任务调用时复制，以存储特定于该调用的状态。静态任务的所有变量都是静态的，即对于模块实例中声明的每个声明的局部变量，都有一个对应的单个变量，而不管任务的并发激活次数。但是，模块的不同实例中的静态任务将与彼此具有单独的存储。

静态任务中声明的变量，包括输入、输出和 inout 类型参数，将在调用之间保留其值。它们将初始化为 6.8 中描述的默认初始化值。

自动任务中声明的变量，包括输出类型参数，将在执行进入其作用域时初始化为默认初始化值。输入和 inout 类型参数将初始化为传递给任务使能语句中对应于这些参数的表达式中的值。

因为自动任务中声明的变量在任务调用结束时被释放，所以不能在可能在此后引用它们的某些构造中使用它们：
 - 不能使用非阻塞赋值或过程连续赋值为它们赋值。
 - 不能通过过程连续赋值或过程强制语句引用它们。
 - 不能在非阻塞赋值的内部赋值事件控制中引用它们。
 - 不能使用系统任务（如 `$monitor` 和 `$dumpvars`）跟踪它们。

## 13.4 函数
函数的主要目的是返回一个值，该值将用于表达式中。也可以使用 void 函数代替任务来定义在单个时间步骤内执行并返回的子例程。本节的其余部分解释了如何定义和使用函数。

函数有一些限制，以确保它们在不挂起启用它们的进程的情况下返回。以下规则应该规范它们的使用，13.4.4 中有例外：
 - 函数不应包含任何时间控制语句。也就是说，任何包含 `#`, `##`, `@`, `fork-join`, `fork-join_any`, `wait`, `wait_order` 或 `expect` 的语句。
 - 函数不应启用任务，无论这些任务是否包含时间控制语句。
 - 函数可以启用细粒度过程控制方法来挂起自己或另一个过程（见 9.7）。

定义函数的语法如下 13-2：
---
```verilog
function_declaration ::= function [ lifetime ] function_body_declaration // from A.2.6
function_body_declaration ::= 
function_data_type_or_implicit 
[ interface_identifier . | class_scope ] function_identifier ;
{ tf_item_declaration } 
{ function_statement_or_null } 
endfunction [ : function_identifier ] 
| function_data_type_or_implicit 
[ interface_identifier . | class_scope ] function_identifier ( [ tf_port_list ] ) ;
{ block_item_declaration } 
{ function_statement_or_null } 
endfunction [ : function_identifier ] 
function_data_type_or_implicit ::= 
data_type_or_void 
| implicit_data_type 
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
signing ::= signed | unsigned
lifetime ::= static | automatic // from A.2.1.3
// 13) 当使用 struct 或 union 关键字与 packed 维度时，应使用 packed 关键字。
// 14) 当在网声明中使用 type_reference 时，应在其前面加上网类型关键字；当在变量声明中使用时，应在其前面加上 var 关键字。
```
---
语法 13-2—函数语法（摘自附录 A）

为了指示函数的返回类型，其声明可以包含显式的 `data_type_or_void`，也可以使用隐式语法，该语法仅指示打包维度的范围，以及可选的符号。当使用隐式语法时，返回类型与如果隐式语法紧接着 `logic` 关键字一样。特别地，隐式语法可以为空，此时返回类型是逻辑标量。函数也可以是 void，没有返回值（见 13.4.1）。

函数声明具有形式参数，形式参数可以在括号中（类似于 ANSI C）或在声明和方向中指定。

```verilog
function logic [15:0] myfunc1(int x, int y);
    ...
endfunction

function logic [15:0] myfunc2;
    input int x;
    input int y;
    ...
endfunction
```

函数可以有与任务相同的形式参数。函数参数方向如下：
 - `input` // 在开始时复制值
 - `output` // 在结束时复制值
 - `inout` // 在开始时复制值，在结束时复制值
 - `ref` // 传递引用（见 13.5.2）

如果未指定方向，则默认方向为 input。一旦给出方向，后续的形式参数默认为相同的方向。在下面的示例中，形式参数 a 和 b 默认为输入，u 和 v 都是输出：

```verilog
function logic [15:0] myfunc3(int a, int b, output logic [15:0] u, v);
    ...
endfunction
```

每个形式参数都有一个数据类型，可以显式声明或从前一个参数继承。如果未显式声明数据类型，则默认数据类型为 `logic`，如果是第一个参数或参数方向明确指定。否则，数据类型从前一个参数继承。数组可以指定为函数的形式参数。例如：

```verilog
function [3:0][7:0] myfunc4(input [3:0][7:0] a, b[3:0]);
    ...
endfunction
```

在事件表达式、过程连续赋值内的表达式或不在过程语句内的表达式中调用具有输出、inout 或 ref 参数的函数是非法的。但是，在此上下文中，const ref 函数参数是合法的（见 13.5.2）。

函数头和 `endfunction` 之间可以写多个语句。语句按顺序执行，就像它们被包含在 `begin` .... `end` 组中一样。也可以完全没有语句，此时函数返回与函数同名的隐式变量的当前值。

### 13.4.1 返回值和 void 函数
函数定义应隐式声明一个与函数同名的变量，该变量是函数内部的变量。此变量的类型与函数返回值相同。函数返回值可以通过使用 `return` 语句或将值分配给与函数同名的内部变量来指定。例如：

```verilog
function [15:0] myfunc1(input [7:0] x, y);
    myfunc1 = x * y - 1; // 返回值分配给函数名
endfunction

function [15:0] myfunc2(input [7:0] x, y);
    return x * y - 1; // 使用 return 语句指定返回值
endfunction
```

`return` 语句将覆盖分配给函数名的任何值。当使用 `return` 语句时，非空函数应指定与返回相关的表达式。

函数返回值可以是结构或联合。在这种情况下，函数内部使用以函数名开头的层次名称解释为返回值的成员。如果函数名在函数外部使用，则该名称表示整个函数的范围。如果函数名在层次名称中使用，它还表示整个函数的范围。

函数可以声明为 void 类型，不具有返回值。函数调用可以用作表达式，除非是 void 类型，这是语句：

```verilog
a = b + myfunc1(c, d); // 调用 myfunc1（上面定义）作为表达式
myprint(a); // 调用 myprint（下面定义）作为语句

function void myprint(int a);
    ...
endfunction
```

返回值的函数可以用于赋值或表达式。将非空函数调用为无返回值调用是合法的，但会发出警告。通过将函数调用转换为 void 类型，可以将函数用作语句并丢弃返回值，而不会发出警告。

```verilog
void'(some_function());
```

在声明函数的作用域内声明具有与函数相同名称的其他对象是非法的。在函数作用域内声明具有与函数相同名称的其他对象也是非法的。

### 13.4.2 静态和自动函数
在模块、接口、程序或包中定义的函数默认为静态函数，所有声明的项都是静态分配的。这些项将在所有并发执行的函数之间共享。

函数可以定义为使用自动存储，使用以下两种方式：
 - 作为函数声明的一部分使用可选的 automatic 关键字显式声明。
 - 通过定义为自动的模块、接口、程序或包中定义函数隐式声明。

在类中定义的函数始终是自动的（见 8.6）。

自动函数是可重入的，所有函数声明都为每个并发函数调用动态分配。自动函数项不能通过层次引用访问。自动函数可以通过其层次名称调用。

在静态函数或自动函数中声明特定的局部变量为 `automatic` 或 `static`。

以下示例定义了一个名为 `factorial` 的函数，返回一个整数值。`factorial` 函数是迭代调用的，结果被打印。

```verilog
module tryfact;
    // 定义函数
    function automatic integer factorial(input [31:0] operand);
        if (operand >= 2) 
            factorial = factorial(operand - 1) * operand;
        else
            factorial = 1;
    endfunction: factorial

    // 测试函数
    integer result;
    initial begin
        for (int n = 0; n <= 7; n++) begin
            result = factorial(n);
            $display("%0d factorial=%0d", n, result);
        end
    end
endmodule: tryfact
```

模拟结果如下：

```
0 factorial=1
1 factorial=1
2 factorial=2
3 factorial=6
4 factorial=24
5 factorial=120
6 factorial=720
7 factorial=5040
```

### 13.4.3 常量函数
常量函数是正常函数的一个子集，应满足以下约束：
 - 常量函数不应具有输出、inout 或 ref 参数。
 - void 函数不应是常量函数。
 - DPI 导入函数（见 35.2.1）不应是常量函数。
 - 常量函数不应包含直接在函数返回后执行的事件调度语句。
 - 常量函数不应包含任何 fork 结构。
 - 常量函数不应包含任何层次引用。
 - 常量函数中调用的任何函数都应是当前模块的常量函数。
 - 在常量函数中调用的任何系统函数都应在常量表达式中允许使用（见 11.2.1）。这包括 `$bits` 和数组查询函数。对其他系统函数的调用是非法的。
 - 常量函数中的所有系统任务调用都将被忽略。
 - 函数中使用的所有参数值都应在调用常量函数调用之前定义（即，在常量函数调用的原始位置使用的任何参数使用都构成该参数在原始常量函数调用点的使用）。常量函数可以引用包或 `$unit` 中定义的参数。
 - 函数中使用的所有不是参数或函数的标识符都应在当前函数中声明。
 - 如果常量函数使用任何直接或间接受 defparam 语句（见 23.10.1）影响的参数值，则结果将是未定义的。这可能会产生错误，或者常量函数可能返回不确定的值。
 - 常量函数不应在 generate 块（见 27 章）中声明。
 - 常量函数本身不应在任何需要常量表达式的上下文中使用常量函数。
 - 常量函数可以具有默认参数值（见 13.5.3），但是任何这样的默认参数值都应是常量表达式。

常量函数调用用于支持在实例化时间构建值的复杂计算（见 3.12）。常量函数调用是一个本地于调用模块或包或 `$unit` 的常量函数的函数调用，其中函数的参数都是常量表达式（见 11.2.1）。

常量函数调用在实例化时间计算。它们的执行对于在模拟时间或在多次实例化时间调用之间使用的变量的初始值没有影响。在这些情况下，变量的初始化与正常仿真一样。

以下示例定义了一个名为 `clogb2` 的函数，返回一个整数，其值为以 2 为底的对数的上限。

```verilog
module ram_model (address, write, chip_select, data);
    parameter data_width = 8;
    parameter ram_depth = 256;
    localparam addr_width = clogb2(ram_depth);
    input [addr_width - 1:0] address;
    input write, chip_select;
    inout [data_width - 1:0] data;

    // 定义 clogb2 函数
    function integer clogb2 (input [31:0] value);
        value = value - 1;
        for (clogb2 = 0; value > 0; clogb2 = clogb2 + 1)
            value = value >> 1;
    endfunction

    logic [data_width - 1:0] data_store[0:ram_depth - 1]; 
    // 其余的 ram 模型
endmodule: ram_model
```

具有分配的参数的 `ram_model` 的实例如下：

```verilog
ram_model #(32,421) ram_a0(a_addr,a_wr,a_cs,a_data); 
```

### 13.4.4 由函数调用生成的后台进程
函数应在不延迟的情况下执行。因此，调用函数的进程应立即返回。函数内部不阻塞的语句应该是允许的；特别地，非阻塞赋值、事件触发、时钟驱动和 fork-join_none 结构应该是允许的。

调用试图调度事件的函数，这些事件在函数返回后才能变为活动，应该是允许的，前提是调用函数的线程是由初始过程、始终过程或从这些过程中的一个创建的 fork 块，并且在允许副作用的上下文中。当这些规定没有得到满足时，实现应该在编译时或运行时发出错误。

在函数内部，fork-join_none 结构可以包含任何在任务内合法的语句。以下是函数中 fork-join_none 的合法和非法用法的示例：

```verilog
class IntClass;
    int a;
endclass

IntClass address=new(), stack=new();

function automatic bit watch_for_zero( IntClass p );
    fork
        forever @p.a begin
            if ( p.a == 0 ) $display (“Unexpected zero”);
        end
    join_none
    return ( p.a == 0 );
endfunction

function bit start_check();
    return ( watch_for_zero( address ) | watch_for_zero( stack ) );
endfunction

bit y = watch_for_zero( stack ); // 非法

initial if ( start_check() ) $display ( “OK”); // 合法

initial fork
    if (start_check() ) $display( “OK too”); // 合法
join_none
```

## 13.5 子程序调用和参数传递
任务和 void 函数作为过程块中的语句调用（见 9.2）。非空 *函数调用* 可以作为表达式的操作数。

调用子程序的语法如下 13-3：
---
```verilog
subroutine_call_statement ::= // from A.6.9
subroutine_call ;
| void ' ( function_subroutine_call ) ;
subroutine_call ::= // from A.8.2
tf_call 
| system_tf_call 
| method_call 
| [ std:: ] randomize_call 
tf_call37 ::= ps_or_hierarchical_tf_identifier { attribute_instance } [ ( list_of_arguments ) ] 
list_of_arguments ::= 
[ expression ] { , [ expression ] } { , . identifier ( [ expression ] ) } 
| . identifier ( [ expression ] ) { , . identifier ( [ expression ] ) } 
ps_or_hierarchical_tf_identifier ::= // from A.9.3
[ package_scope ] tf_identifier 
| hierarchical_tf_identifier 
// 37) 除非子程序是任务、void 函数或类方法，否则在 tf_call 中省略括号是非法的。
// 如果子程序是非空类函数方法，如果调用是直接递归的，则省略括号是非法的。
```
---
语法 13-3—任务或函数调用语法（摘自附录 A）

如果子程序中的参数声明为输入，则子程序调用中的相应表达式可以是任何表达式。参数列表中表达式的计算顺序是未定义的。

如果子程序中的参数声明为输出或 inout，则子程序调用中的相应表达式应限制为在过程赋值的左侧有效的表达式（见 10.4）。

子程序调用的执行将从调用列出的参数中传递输入值。子程序返回的执行将从输出和 inout 类型参数中传递值到子程序调用中的相应变量。

SystemVerilog 提供了两种传递参数给任务和函数的方法：按值传递和按引用传递。参数也可以按名称绑定，也可以按位置绑定。子程序参数也可以给出默认值，允许调用子程序时不传递参数。

### 13.5.1 按值传递
按值传递是将参数值复制到子程序的默认机制。这个参数传递机制通过将参数值复制到子程序的区域来工作。如果子程序是自动的，则子程序在其堆栈中保留参数的本地副本。如果参数在子程序中更改，则更改对子程序外部不可见。当参数很大时，复制参数可能是不希望的。此外，程序有时需要共享一个未声明为全局的公共数据。

例如，调用以下函数每次调用时都会复制 1000 个字节。

```verilog
function automatic int crc( byte packet [1000:1] );
    for( int j= 1; j <= 1000; j++ ) begin
        crc ^= packet[j];
    end
endfunction
```

### 13.5.2 按引用传递
按引用传递的参数没有复制到子程序区域，而是传递到子程序的原始参数的引用。子程序可以通过引用访问参数数据。传递参数按引用应与等效数据类型匹配（见 6.22.2）。不允许进行强制转换。为了指示参数按引用传递，参数声明之前使用 `ref` 关键字。不允许使用静态生命周期的子程序按引用传递参数。大概的语法如下：

```verilog
subroutine( ref type argument );
```

例如，上面的示例可以写成如下形式：

```verilog
function automatic int crc( ref byte packet [1000:1] );
    for( int j= 1; j <= 1000; j++ ) begin
        crc ^= packet[j];
    end
endfunction
```

如上例所示，只需要添加 `ref` 关键字，其他不需要更改。编译器知道 `packet` 现在通过引用寻址，但用户不需要在调用者或调用点显式地进行这些引用。换句话说，对 `crc` 函数的调用保持不变：

```verilog
byte packet1[1000:1];
int k = crc( packet1 ); // 按值或按引用传递：调用是相同的
```

当参数按引用传递时，调用者和子程序共享参数的相同表示形式；因此，调用者或子程序内部对参数所做的任何更改都应该对彼此可见。传递给子程序的变量的赋值语义是在子程序返回之前立即可见的。

只有以下内容可以按引用传递：
 - 变量
 - 类属性
 - 未打包结构的成员
 - 未打包数组的元素

不允许按引用传递网和网选择。

因为按引用传递的变量可能是自动变量，所以不应该在任何禁止自动变量的上下文中使用 `ref` 参数。

按引用传递的动态数组、队列和关联数组的元素可能在调用子程序完成之前从数组中删除，或者数组可能在更改之前被调整大小。传递给子程序的特定数组元素应在子程序完成之前继续存在。在删除元素之前对数组元素的值进行更改的子程序所做的更改不应在更改之前从数组中删除元素的情况下对外部作用域可见。这些引用应称为 *过时引用*。

对变长数组的以下操作将导致现有元素的引用变为过时引用：
 - 使用隐式或显式 `new[]` 调整动态数组的大小。
 - 使用 `delete()` 方法删除动态数组。
 - 使用 `delete()` 方法删除被引用的关联数组的元素。
 - 通过赋值更新包含被引用元素的队列或动态数组。
 - 使用队列方法删除被引用的队列元素。

按引用传递参数是一种独特的参数传递限定符，不同于输入、输出或 inout。将 `ref` 与任何其他方向限定符结合使用是非法的。例如，以下声明将导致编译器错误：

```verilog
task automatic incr( ref input int a ); // 错误：ref 不能被限定
```

`ref` 参数类似于 `inout` 参数，但 `inout` 参数被复制两次：一次从实际复制到参数，一次从参数复制到实际。传递对象句柄也不例外，并且在作为 `ref` 或 `inout` 参数传递时具有类似的语义。因此，对象句柄的 `ref` 允许更改对象句柄（例如，分配新对象）以及修改对象内容。

为了保护按引用传递的参数免受子程序的修改，可以使用 `const` 限定符与 `ref` 结合使用，以指示参数虽然按引用传递，但是是只读变量。

```verilog
task automatic show ( const ref byte data [] );
    for ( int j = 0; j < data.size ; j++ )
        $display( data[j] ); // 数据可以读取但不能写入
endtask
```

当形式参数声明为 `const ref` 时，子程序不能更改变量，尝试这样做将生成编译器错误。

### 13.5.3 默认参数值
为了处理常见情况或允许未使用的参数，SystemVerilog 允许子程序声明为每个单独参数指定默认值。

在子程序中声明默认参数的语法如下：

```verilog
subroutine( [ direction ] [ type ] argument = default_expression );
```

可选的方向可以是 input、inout、output 或 ref。

默认表达式在包含子程序声明的范围中计算，每次使用默认值时都会计算。如果未使用默认值，则不会计算默认表达式。只允许在 ANSI 样式声明中使用默认值。

当调用子程序时，可以省略具有默认值的参数，并且编译器将插入相应的值。未指定（或为空）的参数可以用作默认参数的占位符。如果用于没有默认值的参数的未指定参数，则编译器将发出错误。

```verilog
task read(int j = 0, int k, int data = 1 );
...
endtask
```

此示例声明了一个具有两个默认参数 j 和 data 的任务 read。然后可以使用各种默认参数调用任务：

```verilog
read( , 5 ); // 等效于 read( 0, 5, 1 );
read( 2, 5 ); // 等效于 read( 2, 5, 1 );
read( , 5, ); // 等效于 read( 0, 5, 1 );
read( , 5, 7 ); // 等效于 read( 0, 5, 7 );
read( 1, 5, 2 ); // 等效于 read( 1, 5, 2 );
read( ); // 错误；k 没有默认值
read( 1, , 7 ); // 错误；k 没有默认值
```

以下示例显示了具有默认表达式的输出参数：

```verilog
module m;
    logic a, w;

    task t1 (output o = a) ; // 默认绑定到 m.a
        ...
    endtask :t1

    task t2 (output o = b) ; // 非法，b 无法解析
        ...
    endtask :t2

    task t3 (inout io = w) ; // 默认绑定到 m.w
        ...
    endtask :t1
endmodule :m

module n;
    logic a;

    initial begin
        m.t1(); // 等效于 m.t1(m.a)，而不是 m.t1(n.a);
        // 在任务结束时，t1.o 的值被复制到 m.a
        m.t3(); // 等效于 m.t3(m.w)
        // 在任务开始时，m.w 的值被复制到 t3.io，t3.io 的值在任务结束时被复制到 m.w
    end
endmodule :n
```

### 13.5.4 按名称绑定参数
SystemVerilog 允许任务和函数的参数按名称绑定，也可以按位置绑定。这允许指定非连续的默认参数，并且可以轻松指定要传递的参数。例如：

```verilog
function int fun( int j = 1, string s = "no" );
    ...
endfunction
```

fun 函数可以如下调用：

```verilog
fun( .j(2), .s("yes") ); // fun( 2, "yes" );
fun( .s("yes") ); // fun( 1, "yes" );
fun( , "yes" ); // fun( 1, "yes" );
fun( .j(2) ); // fun( 2, "no" );
fun( .s("yes"), .j(2) ); // fun( 2, "yes" );
fun( .s(), .j() ); // fun( 1, "no" );
fun( 2 ); // fun( 2, "no" );
fun( ); // fun( 1, "no" );
```

如果参数有默认值，则它们被视为模块实例的参数。如果参数没有默认值，则应给出，否则编译器将发出错误。

如果在单个子例程调用中指定了位置参数和命名参数，则所有位置参数应在命名参数之前。然后，使用与上面相同的示例：

```verilog
fun( .s("yes"), 2 ); // 非法
fun( 2, .s("yes") ); // OK
```

### 13.5.5 可选参数列表
当 void 函数或类函数方法未指定参数时，空括号 `()` 在子程序名称后是可选的。这对于需要参数的任务、void 函数和类方法，当所有参数都有指定的默认值时，也是如此。在不是层次限定的直接递归非空类函数方法调用中，省略括号是非法的。

## 13.6 导入和导出函数
SystemVerilog 提供了直接编程接口（DPI），允许将外部语言子例程（如 C 函数）导入到 SystemVerilog 中。导入的子例程与 SystemVerilog 子例程一样调用。SystemVerilog 任务和函数也可以导出到外部语言。有关 DPI 的详细信息，请参见第 35 章。

## 13.7 任务和函数名称
任务和函数名称遵循稍微不同的规则解析，这些规则与其他引用不同。即使作为简单名称使用，任务或函数名称也遵循向上层次的名称解析规则的修改形式。这意味着可以解析对在同一或封闭范围中定义的任务或函数的“前向”引用。有关控制任务和函数名称解析的规则，请参见 23.8.1。

## 13.8 参数化任务和函数
SystemVerilog 提供了一种创建参数化任务和函数（也称为 *参数化子例程*）的方法。参数化子例程允许用户通用地指定或定义实现。在使用该子例程时，可以提供完全定义其行为的参数。这允许只编写和维护一个定义，而不是多个具有不同数组大小、数据类型和变量宽度的子例程。

实现参数化子例程的方法是通过在参数化类中使用静态方法（见 8.10 和 8.25）。以下通用编码器和解码器示例显示了如何使用静态类方法以及类参数化来实现参数化子例程。该示例有一个类，其中包含两个子例程，在本例中共享参数化。可以声明类为虚拟类，以防止对象构造并强制方法的严格静态使用。

```verilog
virtual class C#(parameter DECODE_W, parameter ENCODE_W = $clog2(DECODE_W));
    static function logic [ENCODE_W-1:0] ENCODER_f
    (input logic [DECODE_W-1:0] DecodeIn);
        ENCODER_f = '0;
        for (int i=0; i<DECODE_W; i++) begin
            if(DecodeIn[i]) begin
                ENCODER_f = i[ENCODE_W-1:0];
                break;
            end
        end
    endfunction

    static function logic [DECODE_W-1:0] DECODER_f
    (input logic [ENCODE_W-1:0] EncodeIn);
        DECODER_f = '0;
        DECODER_f[EncodeIn] = 1'b1;
    endfunction
endclass
```

类 C 包含两个静态子例程，ENCODER_f 和 DECODER_f。每个子例程通过重用类参数 DECODE_W 和 ENCODE_W 进行参数化。参数 ENCODE_W 的默认值由使用系统函数 $clog2 确定（见 20.8.1）。这些参数在子例程中用于指定编码器的大小和解码器的大小。

```verilog
module top ();
    logic [7:0] encoder_in;
    logic [2:0] encoder_out;
    logic [1:0] decoder_in;
    logic [3:0] decoder_out;

    // 编码器和解码器输入赋值
    assign encoder_in = 8'b0100_0000;
    assign decoder_in = 2'b11;

    // 编码器和解码器函数调用
    assign encoder_out = C#(8)::ENCODER_f(encoder_in);
    assign decoder_out = C#(4)::DECODER_f(decoder_in);

    initial begin
        #50;
        $display("Encoder input = %b Encoder output = %b\n", 
            encoder_in, encoder_out );
        $display("Decoder input = %b Decoder output = %b\n", 
            decoder_in, decoder_out );
    end
endmodule
```

顶层模块首先定义了一些在本例中使用的中间变量，然后为编码器和解码器输入分配了常量值。通用编码器 ENCODER_f 的子例程调用使用了特定实例的解码器宽度值 8，该值代表编码器的特定实例的解码器宽度值，同时传递输入编码值 encoder_in。此表达式使用静态类范围解析运算符“`::`”（见 8.23）来访问编码器子例程。通用解码器 DECODER_f 的子例程调用类似，使用参数值 4。
