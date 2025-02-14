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
 - 与另一个类对象或 null 的相等性（`==`）、不等性（`!=`）。被比较的对象之一必须与另一个对象赋值兼容。
 - 与另一个类对象或 null 的 case 相等性（`===`）、case 不等性（`!==`）（与 `==` 和 `!=` 的语义相同）。
 - 条件运算符（见 11.4.11）。
 - 类对象的赋值，其类数据类型与目标类对象赋值兼容。
 - 赋值为 `null`。

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

## 8.8 类型构造函数调用
---
```verilog
class_new19 ::= // from A.2.4
[ class_scope ] new [ ( list_of_arguments ) ] 
| new expression 
// 19) 在浅拷贝中，表达式应该求值为对象句柄。
```
---
语法 8-2—调用构造函数（摘自附录 A）

在本章的早期部分描述的 new 的用法要求要构造的对象的类型与赋值目标的类型匹配。另一种构造函数调用形式，*类型构造函数调用*，在 new 关键字之前立即添加 *类作用域*，独立于赋值目标指定构造的对象的类型。指定的类型应与目标赋值兼容。

以下示例说明了类型构造函数调用。`extends` 关键字在 8.13 中描述。超类类型的概念在 8.15 中描述。
```verilog
class C; . . . endclass
class D extends C; . . . endclass
C c = D::new; // 超类类型 C 的变量 c 现在引用类型 D 的新构造对象
```

注意：类型构造函数调用的效果就像声明了一个类型为 D 的临时变量，构造了该变量，然后将其复制到变量 c，如下面的示例片段所示：
```verilog
D d = new;
C c = d;
```

类型构造函数调用应创建并初始化指定类型的新对象。创建和初始化新对象应与 8.7 中描述的普通构造函数完全相同。如果适当，可以像普通构造函数一样传递参数给类型构造函数调用。

如果要构造的对象类型是参数化类（如 8.25 中所述），则指定的类型可以具有参数特化。以下示例继续前面的示例，说明了参数化类的类型构造函数调用，并说明了如何传递参数给构造函数，如 8.7 中所述。
```verilog
class E #(type T = int) extends C;
    T x;
    function new(T x_init);
        super.new();
        x = x_init;
    endfunction
endclass

initial begin
    c = E #(.T(byte))::new(.x_init(5));
end
```

## 8.9 静态类属性
前面的示例仅声明了实例类属性。类的每个实例（即类型为 Packet 的每个对象）都有自己的每个变量的副本。有时只需要一个变量的版本，所有实例都可以访问。使用关键字 `static` 创建这些类属性。因此，例如，在以下情况下，所有类的实例都需要访问一个共享的文件描述符：
```verilog
class Packet ;
    static integer fileID = $fopen( "data", "r" );
```

现在，fileID 将被创建并初始化一次。此后，每个 Packet 对象都可以以通常的方式访问文件描述符：
```verilog
Packet p;
c = $fgetc( p.fileID );
```

静态类属性可以在不创建该类型的对象的情况下使用。

## 8.10 静态方法
方法可以声明为 `static`。静态方法受到所有类作用域和访问规则的约束，但行为类似于可以在类外部调用的常规子例程，即使没有类实例化。静态方法没有访问非静态成员（类属性或方法）的权限，但可以直接访问同一类的静态类属性或调用静态方法。在静态方法的主体中访问非静态成员或特殊的 this 句柄是非法的，并导致编译器错误。静态方法不能是虚方法。
```verilog
class id;
    static int current = 0;
    static function int next_id();
        next_id = ++current; // 访问静态类属性是允许的
    endfunction
endclass
```

静态方法与具有静态生命周期的任务不同。前者指的是方法在类内的生命周期，而后者指的是任务内参数和变量的生命周期。
```verilog
class TwoTasks;
    static task t1(); ... endtask // 具有自动变量生命周期的静态类方法
    task static t2(); ... endtask // 非法：具有静态变量生命周期的非静态类方法
endclass
```

## 8.11 This
`this` 关键字用于明确地引用当前实例的类属性、值参数、本地值参数或方法。this 关键字表示一个预定义的对象句柄，用于引用调用 this 的子例程的对象。this 关键字只能在非静态类方法、约束、内联约束方法或嵌入在类中的 covergroup 中使用（参见 19.4）；否则，将发出错误。例如，以下声明是编写初始化任务的常见方法：
```verilog
class Demo ;
    integer x;
    function new (integer x); 
        this.x = x;
    endfunction
endclass
```

现在，x 既是类的属性，也是函数 new 的参数。在函数 new 中，对 x 的未限定引用应通过查看最内层作用域解析，即在这种情况下，子例程参数声明。要访问实例类属性，它应该使用 this 关键字限定，以引用当前实例。

注意：在编写方法时，成员可以用 this 限定来引用当前实例，但通常是不必要的。

## 8.12 赋值、重命名和复制
声明类变量只创建对象所知的名称。因此，
```verilog
Packet p1;
```

只创建一个变量 p1，可以保存类 Packet 的对象的句柄，但 p1 的初始值是 null。直到创建了 Packet 类型的实例，对象才存在，p1 才包含实际句柄。

```verilog
p1 = new;
```

因此，如果声明另一个变量并将旧句柄 p1 赋给新句柄，如下所示：
```verilog
Packet p2;
p2 = p1;
```

那么仍然只有一个对象，可以用 p1 或 p2 两个名称引用。在这个例子中，new 只执行了一次，因此只创建了一个对象。

然而，如果将前面的示例重写如下，将复制 p1：
```verilog
Packet p1;
Packet p2;
p1 = new;
p2 = new p1;
```

最后一条语句执行了第二次 new，从而创建了一个新对象 p2，其类属性从 p1 复制。这称为*浅拷贝*。所有变量都被复制，包括整数、字符串、实例句柄等。对象不会被复制，只会复制它们的句柄；如前所述，已创建了两个对象的名称。即使类声明包括实例化运算符 new，也是如此。

使用类型构造函数调用进行浅拷贝是非法的（参见 8.8）。

浅拷贝执行如下：
1. 为要复制的类类型分配对象。此分配不应调用对象的构造函数或执行任何变量声明初始化赋值。
2. 将所有类属性，包括用于随机化和覆盖的内部状态，复制到新对象。对象句柄被复制；这包括覆盖组对象的对象句柄（参见第 19 章）。一个例外是对于嵌入式覆盖组（参见 19.4），新对象中的对象句柄应设置为 null。随机化的内部状态包括随机数生成器（RNG）状态、约束的 constraint_mode 状态、随机变量的 rand_mode 状态和 randc 变量的循环状态（参见第 18 章）。
3. 将指向新创建对象的句柄分配给左侧的变量。

注意：浅拷贝不创建覆盖对象（covergroup 实例），结果新对象的属性没有被覆盖。

```verilog
class baseA ;
    integer j = 5; 
endclass

class B ;
    integer i = 1;
    baseA a = new;
endclass

class xtndA extends baseA; 
    rand int x;
    constraint cst1 { x < 10; }
endclass

function integer test;
    xtndA xtnd1;
    baseA base2, base3;
    B b1 = new; // 创建类 B 的对象
    B b2 = new b1; // 创建一个对象是 b1 的拷贝
    b2.i = 10; // i 在 b2 被改变，但是在 b1 中没有
    b2.a.j = 50; // 改变 a.j，b1 和 b2 共享
    test = b1.i; // test 被设为 1 (b1.i 没有变化)
    test = b1.a.j; // test 被设为 50 (a.j 变化了)
    xtnd1 = new; // 创建类 xtndA 的新实例
    xtnd1.x = 3;
    base2 = xtnd1; // base2 指向 xtnd1
    base3 = new base2; // 创建 xtnd1 的浅拷贝
endfunction
```

在最后一个语句，base3 被分配为 base2 的浅拷贝。base3 的类型是基类 baseA 的句柄。当执行了浅拷贝，变量包含子类 xtndA 的实例的句柄。浅拷贝创建被引用对象的复制，导致一个子类 xntdA 的复制实例。这个实例的句柄随后被赋值给 base3。

有几件事值得注意。首先，类属性和实例化对象可以在类声明中直接初始化。其次，浅拷贝不复制对象。第三，实例资格可以根据需要链接到对象内部或通过对象进行访问：
```verilog
b1.a.j // 访问 a，这是 b1 的属性
p.next.next.val // 通过一系列句柄链接到 val
```
要进行完整（深度）复制，复制所有内容（包括嵌套对象），通常需要定制代码。例如:
```verilog
Packet p1 = new;
Packet p2 = new;
p2.copy(p1);
```
其中 copy（Packet p）是一个自定义方法，用于将指定为其参数的对象复制到其实例中。

## 8.13 继承和子类
前面的小节定义了一个名为 Packet 的类。可以扩展这个类，使数据包可以链接到一个列表中。一种解决方案是创建一个名为 LinkedPacket 的新类，其中包含一个类型为 Packet 的变量 packet_c。

要引用 Packet 的类属性，需要引用变量 packet_c。
```verilog
class LinkedPacket;
    Packet packet_c;
    LinkedPacket next;
    function LinkedPacket get_next();
        get_next = next;
    endfunction
endclass
```

因为 LinkedPacket 是 Packet 的一种特殊形式，更优雅的解决方案是扩展类创建一个新的子类，该子类继承了基类的成员。因此，例如：
```verilog
class LinkedPacket extends Packet;
    LinkedPacket next;
    function LinkedPacket get_next();
        get_next = next;
    endfunction
endclass
```

现在，Packet 的所有方法和类属性都是 LinkedPacket 的一部分（就好像它们是在 LinkedPacket 中定义的），并且 LinkedPacket 具有额外的类属性和方法。

基类的方法也可以被覆盖以更改其定义。

SystemVerilog 提供的机制称为 *单继承*，即每个类都是从单个基类派生的。

## 8.14 覆盖成员
子类对象也是其基类的合法代表对象。例如，每个 LinkedPacket 对象都是一个完全合法的 Packet 对象。

LinkedPacket 对象的句柄可以分配给 Packet 变量：
```verilog
LinkedPacket lp = new;
Packet p = lp;
```

在这种情况下，对 p 的引用访问 Packet 类的方法和类属性。因此，例如，如果 LinkedPacket 中的类属性和方法被覆盖，那么通过 p 引用的这些覆盖成员将得到 Packet 类中的原始成员。从 p，LinkedPacket 中的新成员和所有覆盖的成员现在被隐藏。

```verilog
class Packet;
    integer i = 1;
    function integer get();
        get = i;
    endfunction
endclass

class LinkedPacket extends Packet;
    integer i = 2;
    function integer get();
        get = -i;
    endfunction
endclass

LinkedPacket lp = new;
Packet p = lp;
j = p.i; // j = 1，而不是 2
j = p.get(); // j = 1，而不是 -1 或 -2
```

要通过基类对象（例如 p）调用覆盖的方法，该方法需要声明为虚方法（参见 8.20）。

## 8.15 Super
`super` 关键字用于从派生类中引用基类的成员、类值参数或本地值参数。当这些被派生类覆盖时，需要使用 super 来访问基类的成员、值参数或本地值参数。通过 super 访问值参数或本地值参数的表达式不是常量表达式。

```verilog
class Packet; // 基类
    integer value;
    function integer delay();
        delay = value * value;
    endfunction
endclass

class LinkedPacket extends Packet; // 派生类
    integer value;
    function integer delay();
        delay = super.delay() + value * super.value;
    endfunction
endclass
```

成员、值参数或本地值参数可以声明为向上一级或被继承的类。没有办法到达更高的级别（例如，super.super.count 是不允许的）。

子类（或派生类）是当前类的扩展，而超类（基类）是当前类从原始基类开始的扩展。

super.new 调用应该是构造函数中执行的第一条语句。这是因为在当前类之前应该初始化超类，如果用户代码没有提供初始化，编译器将自动插入对 super.new 的调用。

## 8.16 强制转换
将子类类型的表达式分配给继承树中更高的类类型的变量（超类或祖先）始终是合法的。直接将超类类型的变量分配给其子类类型的变量是非法的。但是，可以使用 $cast 将超类句柄分配给子类类型的变量，前提是超类句柄引用的对象与子类变量赋值兼容。

为了检查分配是否合法，使用动态转换函数 $cast（参见 6.24.2）。$cast 的原型如下：
```verilog
function int $cast( singular dest_var, singular source_exp );
```

或
```verilog
task $cast( singular dest_var, singular source_exp );
```

当 $cast 应用于类句柄时，只有三种情况下才会成功：
1. 源表达式和目标类型是赋值兼容的，即目标是源表达式的相同类型或超类。
2. 源表达式的类型与目标类型是强制转换兼容的，即：
    - 源表达式的类型是目标类型的超类，或
    - 源表达式的类型是接口类（参见 8.26）并且源是与目标类型赋值兼容的对象。这种类型的赋值需要运行时检查，由 $cast 提供。
3. 源表达式是字面常量 null。

在所有其他情况下，$cast 将失败，特别是当源和目标类型不是强制转换兼容时，即使源表达式求值为 null 也是如此。

当 $cast 成功时，它执行赋值。否则，错误处理如 6.24.2 中所述。

## 8.17 链式构造函数
当实例化子类时，将调用类方法 new()。在计算函数中定义的任何代码之前，new() 执行的第一个操作是调用其超类的 new() 方法，以及上述继续上升的继承层次。因此，所有构造函数都被调用，按正确的顺序，从根基类开始，以当前类结束。类属性初始化在此序列中发生，如 8.7 中所述。

如果超类的初始化方法需要参数，有两种选择：始终提供相同的参数或使用 super 关键字。如果参数始终相同，则可以在扩展类时指定参数：
```verilog
class EtherPacket extends Packet(5);
```

这将 5 传递给与 Packet 关联的 new 程序。

更一般的方法是使用 super 关键字调用超类构造函数：
```verilog
function new();
    super.new(5);
endfunction
```

要使用此方法，`super.new()` 调用应该是函数 `new` 中的第一个可执行语句。

如果参数在扩展类时指定，则子类构造函数不应包含 `super.new()` 调用。编译器将自动插入对 `super.new()` 的调用，就像子类构造函数不包含 `super.new()` 调用一样（参见 8.15）。

注意：将类构造函数声明为 `local` 方法会使该类无法扩展，因为在子类中引用 `super.new()` 将是非法的。

## 8.18 数据隐藏和封装
在 SystemVerilog 中，未限定的类属性和方法是公共的，可以被任何访问对象名称的人访问。通常，希望通过隐藏其名称来限制对类属性和方法的访问。这使得其他程序员无法依赖于特定的实现，还可以防止对类属性的意外修改。当所有数据被隐藏（即仅通过公共方法访问）时，代码的测试和维护变得更加容易。

类参数和类本地参数也是公共的。

被标识为 `local` 的成员仅在类内部的方法中可用。此外，这些本地成员在子类中不可见。当然，访问本地类属性或方法的非本地方法可以被继承，并作为子类的方法正常工作。

被标识为 `protected` 的类属性或方法具有本地成员的所有特征，除了它可以被继承；它对子类可见。

在类内部，同一类的不同实例中的本地方法或类属性可以被引用，即使它们在同一类的不同实例中。例如：
```verilog
class Packet;
    local integer i;
    function integer compare (Packet other);
        compare = (this.i == other.i);
    endfunction
endclass
```

封装的严格解释可能会说，other.i 不应该在此数据包内部被访问，因为它是从其实例外部引用的本地类属性。然而，在同一类中，这些引用是允许的。在这种情况下，应该将 this.i 与 other.i 进行比较，并返回逻辑比较的结果。

类成员可以被标识为 `local` 或 `protected`；类属性可以进一步定义为 `const`，方法可以定义为 `virtual`。这些修饰符的指定没有预定义的顺序；但是，每个成员只能出现一次。将成员定义为既是 `local` 又是 `protected`，或重复任何其他修饰符，将是错误的。

## 8.19 常量类属性
类属性可以通过像任何其他 SystemVerilog 变量一样的 `const` 声明变为只读。然而，因为类对象是动态对象，类属性允许两种形式的只读变量：全局常量和实例常量。

全局常量类属性在其声明中包含一个初始值。它们类似于其他 const 变量，因为它们不能在声明之外的任何地方赋值。
```verilog
class Jumbo_Packet;
    const int max_size = 9 * 1024; // 全局常量
    byte payload [];
    function new( int size );
        payload = new[ size > max_size ? max_size : size ];
    endfunction
endclass
```

实例常量在其声明中不包含初始值，只有 const 修饰符。这种常量可以在运行时赋值，但是赋值只能在相应的类构造函数中进行一次。
```verilog
class Big_Packet;
    const int size; // 实例常量
    byte payload [];
    function new();
        size = $urandom % 4096; // 在 new 中只能赋值一次 -> ok
        payload = new[ size ];
    endfunction
endclass
```

通常，全局常量也声明为静态的，因为它们对类的所有实例都是相同的。但是，实例常量不能声明为静态，因为这样做会禁止构造函数中的所有赋值。

## 8.20 虚方法
类方法可以声明为 `virtual`。虚方法是一种基本的多态构造。虚方法应覆盖其所有基类中的方法，而非虚方法只应覆盖该类及其后代中的方法。一种观点是，每个类层次结构中只有一个虚方法的实现，它总是在最新的派生类中。

虚方法为稍后覆盖它的方法提供原型，即通常在方法声明的第一行找到的所有信息：封装标准、参数的类型和数量，以及需要的返回类型。

子类中的虚方法覆盖应具有匹配的参数类型、相同的参数名称、相同的限定符和相同的方向。虚函数的返回类型应该是超类的虚函数的返回类型的：
 - 匹配类型（参见 6.22.1）
 - 派生类型

不需要匹配默认表达式，但是默认的存在应该匹配。

示例 1 说明了虚方法覆盖。
```verilog
class BasePacket;
    int A = 1;
    int B = 2;
    function void printA;
        $display("BasePacket::A is %d", A);
    endfunction : printA
    virtual function void printB;
        $display("BasePacket::B is %d", B);
    endfunction : printB
endclass : BasePacket

class My_Packet extends BasePacket;
    int A = 3;
    int B = 4;
    function void printA;
        $display("My_Packet::A is %d", A);
    endfunction: printA
    virtual function void printB;
        $display("My_Packet::B is %d", B);
    endfunction : printB
endclass : My_Packet

BasePacket P1 = new;
My_Packet P2 = new;

initial begin
    P1.printA; // 显示 'BasePacket::A is 1'
    P1.printB; // 显示 'BasePacket::B is 2'
    P1 = P2; // P1 指向 My_packet 对象
    P1.printA; // 显示 'BasePacket::A is 1'
    P1.printB; // 显示 'My_Packet::B is 4' - 最新的派生方法
    P2.printA; // 显示 'My_Packet::A is 3'
    P2.printB; // 显示 'My_Packet::B is 4'
end
```

示例 2 说明了虚函数返回类型的派生类类型和匹配形式参数类型。在派生类 D 中，虚函数返回类型是 D，是 C 的派生类类型。形式参数数据类型是 T，是预定义类型 int 的匹配数据类型。
```verilog
typedef int T; // T 和 int 是匹配数据类型。

class C;
    virtual function C some_method(int a); endfunction
endclass

class D extends C;
    virtual function D some_method(T a); endfunction
endclass

class E (type Y = logic) extends C;
    virtual function D some_method(Y a); endfunction
endclass

E #() v1; // 非法：类型参数 Y 解析为 logic，不是匹配类型的参数 a
E #(int) v2; // 合法：类型参数 Y 解析为 int
```

虚方法可以覆盖非虚方法，但一旦方法被标识为虚方法，它在覆盖它的任何子类中都应该保持虚方法。在这种情况下，后续声明中可以使用虚关键字，但不是必需的。

## 8.21 抽象类和纯虚方法
可以创建一组类，这些类可以被视为都是从一个公共基类派生的。例如，一个名为 BasePacket 的数据包的公共基类，但是不完整，永远不会被构造。这被称为 *抽象类*。然而，从这个抽象基类中，可以派生出一系列有用的子类，例如 Ethernet 数据包、令牌环数据包、GPS 数据包和卫星数据包。这些数据包可能看起来非常相似，都需要相同的方法集，但在内部细节上可能有很大的不同。

一个基类可以通过将其标识为 `virtual` 来表示为抽象类：
```verilog
virtual class BasePacket;
    ...
endclass
```

抽象类的对象不应该直接构造。它的构造函数只能通过在扩展的非抽象对象中间接调用来间接调用。

抽象类中的虚方法可以声明为原型而不提供实现。这被称为 *纯虚方法*，应该与关键字 `pure` 一起指示，并且不提供方法体。扩展的子类可以通过覆盖纯虚方法来提供实现，覆盖纯虚方法的虚方法具有方法体。

抽象类可以扩展为进一步的抽象类，但是所有纯虚方法应该有覆盖实现，以便被非抽象类扩展。通过为所有方法提供实现，类是完整的，现在可以构造。任何类都可以扩展为抽象类，并且可以提供额外或覆盖的纯虚方法。
```verilog
virtual class BasePacket;
    pure virtual function integer send(bit[31:0] data); // 没有实现
endclass

class EtherPacket extends BasePacket;
    virtual function integer send(bit[31:0] data);
        // body of the function
        ... 
    endfunction
endclass
```

现在，EtherPacket 是一个可以构造其类型的类。

注意：没有语句体的方法仍然是合法的可调用方法。例如，如果函数 send 声明如下，它将有一个实现：
```verilog
virtual function integer send(bit[31:0] data); // 将返回 'x
endfunction
```

## 8.22 多态：动态方法查找
多态允许使用超类类型的变量来保存子类对象，并直接从超类变量引用这些子类的方法。例如，假设 Packet 对象的基类为 BasePacket，BasePacket 定义了所有子类通常使用的公共方法，如 send、receive 和 print。即使 BasePacket 是抽象的，它仍然可以用来声明一个变量：
```verilog
BasePacket packets[100];
```

现在，可以创建各种数据包对象的实例并将其放入数组中：
```verilog
EtherPacket ep = new; // 扩展 BasePacket
TokenPacket tp = new; // 扩展 BasePacket
GPSPacket gp = new; // 扩展 EtherPacket
packets[0] = ep;
packets[1] = tp;
packets[2] = gp;
```

如果数据类型是整数、位和字符串，所有这些类型都不能存储在单个数组中，但是通过多态，可以实现。在这个例子中，因为方法被声明为虚方法，所以可以从超类变量直接访问子类方法，即使编译器在编译时不知道将要加载什么。

例如，packets[1] `packets[1].send();` 将调用与 TokenPacket 类相关联的 send 方法。在运行时，系统将正确地将方法绑定到适当的类。

这是多态在工作中的一个典型例子，提供的功能比非面向对象框架中找到的功能要强大得多。

## 8.23 类作用域解析运算符 ::
类作用域解析运算符 :: 用于指定在类范围内定义的标识符。它的形式如下：
```verilog
class_type :: { class_type :: } identifier
```

作用域解析运算符 :: 的左操作数应该是类类型名称、包名称、覆盖组类型名称、覆盖点名称、交叉名称、typedef 名称或类型参数。当使用类型名称时，名称应在展开后解析为类或覆盖组类型。

因为类和其他作用域可以有相同的标识符，所以类作用域解析运算符 :: 唯一地标识特定类的成员、参数或本地参数。除了消除类作用域标识符的歧义，:: 运算符还允许从类的外部访问静态成员（类属性和方法）、类参数和类本地参数，以及从派生类中访问超类的公共或保护元素。类参数或本地参数是类的公共元素。类作用域参数或本地参数是常量表达式。
```verilog
class Base;
    typedef enum {bin,oct,dec,hex} radix;
    static task print( radix r, integer n ); ... endtask
endclass
...
Base b = new;
int bin = 123;
b.print( Base::bin, bin ); // Base::bin 和 bin 是不同的
Base::print( Base::hex, 66 );
```

在 SystemVerilog 中，类作用域解析运算符适用于类的所有静态元素：静态类属性、静态方法、typedef、枚举、参数、本地参数、约束、结构、联合和嵌套类声明。类作用域解析表达式可以在表达式中读取（在赋值或子例程调用中）、写入（在赋值或子例程调用中）或触发（在事件表达式中）。类作用域还可以用作类型或方法调用的前缀。

与模块一样，类是作用域，可以嵌套。嵌套允许隐藏本地名称和本地资源的本地分配。当需要新类型作为类的实现的一部分时，这通常是有用的。在类作用域内声明的类型有助于防止名称冲突和外部作用域中仅由该类使用的符号。在类作用域内声明的类型是公共的，可以在类外部访问。
```verilog
class StringList;
    class Node; // 链表中节点的嵌套类。
    string name;
    Node link;
endclass

class StringTree;
    class Node; // 二叉树中节点的嵌套类。
    string name;
    Node left, right;
endclass
// StringList::Node 与 StringTree::Node 不同
```

类作用域解析运算符允许以下操作：
 - 从类层次结构外部访问静态公共成员（方法和类属性）。
 - 从派生类中访问超类的公共或保护类成员。
 - 从类的外部或从派生类中访问在类内部声明的约束、类型声明和枚举命名常量。
 - 从类的外部或从派生类中访问在类内部声明的参数和本地参数。

嵌套类应具有与包含类中的方法相同的访问权限。它们对包含类的本地和保护方法和属性具有完全访问权限。嵌套类具有词法作用域、无限定访问类的静态属性和方法、参数和本地参数。除非通过传递给它的句柄或以其他方式可访问，否则嵌套类不得对非静态属性和方法进行隐式访问。没有对外部类的隐式 this 句柄。例如：
```verilog
class Outer;
    int outerProp;
    local int outerLocalProp;
    static int outerStaticProp;
    static local int outerLocalStaticProp;
    class Inner;
        function void innerMethod(Outer h);
            outerStaticProp = 0; // 合法，与 Outer::outerStaticProp 相同
            outerLocalStaticProp = 0; // 合法，嵌套类可以访问外部类的本地
            outerProp = 0; // 非法，对非静态外部的无限定访问
            h.outerProp = 0; // 合法，限定访问。
            h.outerLocalProp = 0; // 合法，限定访问和允许外部类的本地。
        endfunction
    endclass
endclass
```

当使用参数化类名称作为前缀时，类解析运算符具有特殊规则；有关详细信息，请参见 8.25.1。







