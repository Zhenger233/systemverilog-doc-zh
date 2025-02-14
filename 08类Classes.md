# 8. 类
## 8.1 概述
本章描述了以下内容：
 - 类定义
 - 虚类和方法
 - 多态
 - 参数化类
 - 接口类
 - 内存管理

## 8.2 总览
类是一种包含数据和子程序（函数和任务）的类型，这些子程序操作这些数据。类的数据称为 *类属性*，其子程序称为 *方法*；两者都是类的成员。类属性和方法一起定义了某种对象的内容和功能。

例如，数据包可能是一个对象。它可能有一个命令字段、一个地址、一个序列号、一个时间戳和一个数据包有效载荷。此外，可以对数据包执行各种操作：初始化数据包、设置命令、读取数据包的状态或检查序列号。每个数据包都是不同的，但作为一个类，数据包具有可以在定义中捕获的某些固有属性。

```verilog
class Packet ; 
    // 数据或类属性
    bit [3:0] command; 
    bit [40:0] address;
    bit [4:0] master_id;
    integer time_requested;
    integer time_issued;
    integer status;
    typedef enum { ERR_OVERFLOW= 10, ERR_UNDERFLOW = 1123} PCKT_TYPE;
    const integer buffer_size = 100;
    const integer header_size;

    // 初始化
    function new();
        command = 4'd0;
        address = 41'b0;
        master_id = 5'bx; 
        header_size = 10;
    endfunction

    // 方法
    // 公开访问接入点
    task clean(); 
        command = 0; address = 0; master_id = 5'bx; 
    endtask

    task issue_request( int delay );
        // 发送请求到总线
    endtask

    function integer current_status();
        current_status = status; 
    endfunction
endclass
```

面向对象的类扩展允许动态创建和销毁对象。类实例或对象可以通过对象句柄传递，这提供了安全指针功能。对象可以声明为具有输入、输出、inout 或 ref 方向的参数。在每种情况下，传递的参数是对象句柄，而不是对象的内容。

## 8.3 语法
---
```bnf
class_declaration ::= // from A.1.2
[virtual ] class [ lifetime ] class_identifier [ parameter_port_list ] 
[ extends class_type [ ( list_of_arguments ) ] ] 
[ implements interface_class_type { , interface_class_type } ] ;
{ class_item } 
endclass [ : class_identifier] 
interface_class_type ::= ps_class_identifier [ parameter_value_assignment ] 
class_item ::= // from A.1.9
{ attribute_instance } class_property 
| { attribute_instance } class_method 
| { attribute_instance } class_constraint 
| { attribute_instance } class_declaration 
| { attribute_instance } covergroup_declaration 
| local_parameter_declaration ;
| parameter_declaration7 ;
| ;
class_property ::= 
{ property_qualifier } data_declaration 
| const { class_item_qualifier } data_type const_identifier [ = constant_expression ] ;
class_method ::= 
{ method_qualifier } task_declaration 
| { method_qualifier } function_declaration 
| pure virtual { class_item_qualifier } method_prototype ; 
| extern { method_qualifier } method_prototype ;
| { method_qualifier } class_constructor_declaration 
| extern { method_qualifier } class_constructor_prototype 
class_constructor_prototype ::= 
function new [ ( [ tf_port_list ] ) ] ;
class_constraint ::= 
constraint_prototype 
| constraint_declaration 
class_item_qualifier8 ::= 
static
| protected
| local
property_qualifier8
 ::= 
random_qualifier 
| class_item_qualifier 
random_qualifier8 ::= 
rand
| randc
method_qualifier8
 ::= 
[ pure ] virtual
| class_item_qualifier 
method_prototype ::= 
task_prototype 
| function_prototype 
// 7) 在一个 class_item 中的 parameter_declaration，parameter 关键字应该是 localparam 关键字的同义词。
// 8) 在任何一个声明中，只允许 protected 或 local 中的一个，只允许 rand 或 randc 中的一个，static 和/或 virtual 只能出现一次。
```
---
语法 8-1—类语法（摘自附录 A）

## 8.4 对象（类实例）
类定义了一种数据类型。对象是该类的一个实例。通过首先声明一个类类型的变量（保存对象句柄），然后创建该类的对象（使用 new 函数）并将其分配给变量来使用对象。

```verilog
Packet p; // 声明一个类 Packet 的变量
p = new; // 将变量初始化为类 Packet 的一个新分配的对象
```

变量 p 被称为持有类 Packet 对象句柄的对象句柄。

未初始化的对象句柄默认设置为特殊值 `null`。可以通过将其句柄与 `null` 进行比较来检测未初始化的对象。

例如：以下任务 task1 检查对象是否已初始化。如果没有，它通过 `new` 命令创建一个新对象。

```verilog
class obj_example;
...
endclass

task task1(integer a, obj_example myexample);
    if (myexample == null) myexample = new;
endtask
```

通过 `null` 对象句柄访问非静态成员（参见 8.9）或虚方法（参见 8.20）是非法的。通过 `null` 对象进行非法访问的结果是不确定的，实现可能会发出错误。

SystemVerilog 对象使用对象句柄引用。SystemVerilog 对象句柄与 C 指针之间存在一些差异（参见表 8-1）。C 指针允许程序员在使用指针时有很大的自由度。规定了使用 SystemVerilog 对象句柄的规则要严格得多。例如，C 指针可以递增，但 SystemVerilog 对象句柄不能。除了对象句柄，6.14 引入了用于 DPI 的 `chandle` 数据类型（参见第 35 章）。

表 8-1—指针和句柄类型的比较
| 操作 | C 指针 | SV 对象句柄 | SV chandle |
| --- | --- | --- | --- |
| 算术运算（如递增） | 允许 | 不允许 | 不允许 |
| 任意数据类型 | 允许 | 不允许 | 不允许 |
| 空指针解引用 | 错误 | 错误，见上文 | 不允许 |
| 强制转换 | 允许 | 有限 | 不允许 |
| 分配给数据类型的地址 | 允许 | 不允许 | 不允许 |
| 未引用的对象被垃圾回收 | 否 | 是 | 否 |
| 默认值 | 未定义 | null | null |
| 对于类 | （C++） | 允许 | 不允许 |

只有以下操作符对对象句柄有效：
 - 与另一个类对象或 null 的相等性（==）、不等性（!=）。被比较的对象之一必须与另一个对象赋值兼容。
 - 与另一个类对象或 null 的 case 相等性（===）、case 不等性（!==）（与 == 和 != 的语义相同）。
 - 条件运算符（见 11.4.11）。
 - 类对象的赋值，其类数据类型与目标类对象赋值兼容。
 - 赋值为 null。

## 8.5 对象属性和对象参数数据
类属性的数据类型没有限制。对象的类属性可以通过将实例名称与类属性名称相结合来使用。使用前面的示例（参见 8.2），可以如下使用 Packet 对象 p 的属性：

```verilog
Packet p = new;
int var1; 
p.command = INIT;
p.address = $random;
packet_time = p.time_requested;
var1 = p.buffer_size;
```

类枚举名称，除了使用类范围解析运算符访问外，还可以通过将类枚举名称与实例名称限定来访问。

```verilog
initial $display (p.ERR_OVERFLOW);
```

对象的参数数据值也可以通过将类值参数或本地值参数名称与实例名称限定来访问。这样的表达式不是常量表达式。不允许使用类句柄访问数据类型。例如：

```verilog
class vector #(parameter width = 7, type T = int);
endclass
vector #(3) v = new;
initial $display (vector #(3)::T'(3.45)); // 类型转换
initial $display ((v.T)'(3.45)); // 非法
initial $display (v.width);
```

## 8.6 对象方法
可以使用与访问类属性相同的语法来访问对象的方法：
```verilog
Packet p = new;
status = p.current_status();
```

前面的赋值给 status 不能写成如下形式：
```verilog
status = current_status(p);
```

面向对象编程的重点是对象，即数据包，而不是函数调用。此外，对象是自包含的，具有用于操作自身属性的方法。因此，对象不必作为参数传递给 current_status()。类的属性对类的方法自由广泛地可用，但每个方法只访问与其对象相关联的属性，即其实例。

类方法声明的生命周期应为自动。声明为类类型的方法不得具有静态生命周期。

## 8.7 构造函数
SystemVerilog 不需要像 C++ 那样复杂的内存分配和释放。对象的构造是直接的；并且像 Java 那样，垃圾回收是隐式和自动的。不会有内存泄漏或其他常常困扰 C++ 程序员的微妙行为。

SystemVerilog 提供了在创建对象时初始化实例的机制。当创建对象时，例如：
```verilog
Packet p = new;
```

系统执行与类关联的 new 函数：
```verilog
class Packet;
    integer command;
    function new();
        command = IDLE; 
    endfunction
endclass
```

如上所示，`new` 现在在两个非常不同的上下文中使用，具有非常不同的语义。变量声明创建类 Packet 的对象。在创建此实例的过程中，将调用 `new` 函数，其中可以执行任何所需的专门初始化。`new` 函数也称为*类构造函数*。

`new` 操作被定义为没有返回类型的函数，就像任何其他函数一样，它应该是非阻塞的。尽管 `new` 没有指定返回类型，但赋值的左侧确定了返回类型。

如果一个类没有提供显式的用户定义 `new` 方法，将自动提供一个隐式的 `new` 方法。派生类的 `new` 方法应首先调用其基类构造函数 （如 8.15 中所述的 `super.new()`）。在基类构造函数调用（如果有的话）完成后，类中定义的每个属性都将初始化为其显式默认值或未初始化值（如果未提供默认值）。在属性初始化后，将计算用户定义构造函数中的剩余代码。默认构造函数在属性初始化后没有其他效果。在初始化之前，属性的值应为未定义。

例如：
```verilog
class C;
    int c1 = 1;
    int c2 = 1;
    int c3 = 1;
    function new(int a);
        c2 = 2;
        c3 = a;
    endfunction
endclass

class D extends C;
    int d1 = 4;
    int d2 = c2;
    int d3 = 6;
    function new;
        super.new(d3); 
    endfunction
endclass
```

在完成 D 类对象的构造之后，属性如下：
 - c1 的值为 1
 - c2 的值为 2，因为构造函数赋值发生在属性初始化之后
 - c3 的值未定义，因为 D 中的构造函数调用传递了 d3 的值，而 d3 在 super.new(d3) 调用时是未定义的
 - d1 的值为 4
 - d2 的值为 2，因为 super.new 调用完成时 d2 初始化
 - d3 的值为 6

也可以向构造函数传递参数，这允许对象的运行时定制：
```verilog
Packet p = new(STARTUP, $random, $time);
```

在 Packet 中的 new 初始化任务现在可能如下所示：
```verilog
function new(int cmd = IDLE, bit[12:0] adrs = 0, int cmd_time );
    command = cmd;
    address = adrs; 
    time_requested = cmd_time;
endfunction
```

参数的约定与任何其他过程子例调用的约定相同，例如使用默认参数。

构造函数可以声明为 `local` 或 `protected` 方法（参见 8.18）。构造函数不得声明为 `static`（参见 8.10）或 `virtual` 方法（参见 8.20）。

