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

## 8.24 块外声明
将方法定义移出类声明体是方便的。这是通过两个步骤完成的。首先，在类体内，声明方法原型，即它是函数还是任务、任何限定符（`local` 、`protected` 或 `virtual`）以及完整的参数规定加上 `extern` 限定符。`extern` 限定符表示方法的实现可以在声明之外找到。其次，在类声明体外，声明完整的方法（例如，原型但不包括限定符），并将方法名称限定为类名和一对冒号，如下所示：
```verilog
class Packet;
    Packet next;
    function Packet get_next();// 单行
        get_next = next;
    endfunction

    // 块外（extern）声明
    extern protected virtual function int send(int value);
endclass

function int Packet::send(int value);
    // 删除保护虚拟，添加 Packet::
    // 方法体
    ...
endfunction
```

块外方法声明应与原型声明完全匹配，以下情况除外：
 - 方法名称前面加上类名和类作用域解析运算符。
 - 函数返回类型可能还需要在块外声明中添加类作用域，如下所述。
 - 在原型中指定的默认参数值可能在块外声明中省略。如果在块外声明中指定了默认参数值，则原型中应有一个语法上相同的默认参数值。

块外声明应在类声明的相同作用域中声明，并应跟随类声明。如果为特定 `extern` 方法提供了多个块外声明，则会报告错误。

在某些情况下，需要使用类解析运算符来命名方法的返回类型。当块外声明的返回类型在类内部定义时，应使用作用域解析运算符来指示内部返回类型。

```verilog
typedef real T;

class C;
    extern function T f();
    extern function real f2();
endclass

function C::T C::f(); // 返回必须使用作用域解析
    return 1;
endfunction

function real C::f2();
    return 1.0;
endfunction
```

块外方法声明应能够访问类中声明的所有声明。按照正常解析规则，如果类类型在原型之前声明，则原型可以访问类类型。如果原型中引用的标识符未解析为与块外方法声明头部解析的相同声明，则将报告错误。

```verilog
typedef int T;
class C;
    extern function void f(T x);
    typedef real T;
endclass

function void C::f(T x);
endfunction
```

在此示例中，原型方法 f 中的标识符 T 解析为外部范围中的 T 声明。在方法 f 的块外声明中，标识符 T 解析为 C::T，因为块外声明对类 C 中的所有类型都有可见性。由于块外声明中的 T 解析与原型中的解析不匹配，将报告错误。

## 8.25 参数化类
通常，定义一个通用类，其对象可以实例化为具有不同的数组大小或数据类型是有用的。这样可以避免为每个大小或类型编写类似的代码，并允许使用单个规范来实例化根本不同的对象，并且（与 C++ 中的模板类一样）不可互换。

SystemVerilog 参数机制用于参数化类：
```verilog
class vector #(int size = 1);
    bit [size-1:0] a;
endclass
```

然后可以像模块或接口一样实例化此类：
```verilog
vector #(10) vten; // 大小为 10 的对象
vector #(.size(2)) vtwo; // 大小为 2 的对象
typedef vector#(4) Vfour; // 大小为 4 的类
```

当使用类型作为参数时，这个特性尤其有用：
```verilog
class stack #(type T = int);
    local T items[];
    task push( T a ); ... endtask
    task pop( ref T a ); ... endtask
endclass
```

上面的类定义了一个通用 *堆栈* 类，可以实例化为任意类型：
```verilog
stack is; // 默认：int 堆栈
stack#(bit[1:10]) bs; // 10 位向量堆栈
stack#(real) rs; // 实数堆栈
```

任何类型都可以作为参数提供，包括用户定义的类型，如 `class` 或 `struct`。

类的组合和实际参数值的组合称为 *特化*。类的每个特化都有一组独特的 `static` 成员变量（这与 C++ 模板类一致）。要在多个类特化之间共享静态成员变量，它们应该放在一个非参数化的基类中。
```verilog
class vector #(int size = 1);
    bit [size-1:0] a;
    static int count = 0;
    function void disp_count();
        $display( "count: %d of size %d", count, size );
    endfunction
endclass
```

在上面的示例中，变量 count 只能通过相应的 disp_count 方法访问。类 vector 的每个特化都有其自己独特的 count 副本。

特化是特定的通用类与一组唯一参数的组合。两组参数应该是唯一的，除非所有参数都相同，如下所示：
 - 参数是类型参数，两个类型是匹配类型。
 - 参数是值参数，它们的类型和值都相同。

特定通用类的所有匹配特化应该表示相同的类型。通用类的匹配特化集由类声明的上下文定义。因为包中的通用类在整个系统中可见，包中通用类的所有匹配特化都是相同的类型。在其他上下文中，如模块或程序，包含通用类声明的作用域的每个实例都创建一个唯一的通用类，从而定义新的匹配特化集。

通用类不是类型；只有具体特化代表类型。在上面的示例中，类 vector 只有在应用参数后才成为具体类型，例如：
```verilog
typedef vector#(4) Vfour; // 使用默认大小 4
vector#(6) vx; // 使用大小 6
```

为了避免重复特化的声明或创建该类型的参数，应该使用 `typedef`：
```verilog
typedef vector#(4) Vfour;
typedef stack#(Vfour) Stack4;
Stack4 s1, s2; // 声明 Stack4 类型的对象
```

参数化类可以扩展另一个参数化类。例如：
```verilog
class C #(type T = bit); ... endclass // 基类
class D1 #(type P = real) extends C; // T 是 bit（默认）
class D2 #(type P = real) extends C #(integer); // T 是 integer
class D3 #(type P = real) extends C #(P); // T 是 P
class D4 #(type P = C#(real)) extends P; // 对于默认 T 是 real
```

类 D1 使用基类 C 扩展基类的默认类型（bit）参数。类 D2 使用整数参数扩展基类 C。类 D3 使用参数化类型（P）扩展基类 C。类 D4 使用类型参数 P 扩展指定的基类。

当类型参数或 typedef 名称用作基类时，如上面的类 D4，名称应在展开后解析为类类型。

参数化类的默认特化是将参数化类与空参数覆盖列表的特化。对于参数化类 C，默认特化是 `C#()`。除非作为作用域解析运算符的前缀，使用未装饰的参数化类的名称应表示类的默认特化。不是所有参数化类都有默认特化，因为类可能不提供参数默认值。在这种情况下，所有特化应该至少覆盖那些没有默认值的参数。

示例：
```verilog
class C #(int p = 1);
...
endclass

class D #(int p);
...
endclass

C obj; // 合法；等同于 "C#() obj";
D obj; // 非法；D 没有默认特化
```

### 8.25.1 参数化类的类解析运算符
有前缀的类解析运算符即参数化类的未装饰名称（参见 8.25）应该限制在命名参数化类的范围内以及在其块外声明内（参见 8.24）使用。在这种情况下，未装饰的参数化类名称不表示默认特化，而是用于明确引用参数化类的成员。当引用默认特化作为类解析运算符的前缀时，应使用显式默认特化形式 `#()`。

参数化类外的上下文或其块外声明之外的上下文中，类解析运算符可以用于访问任何类参数。在这种上下文中，应使用显式特化形式；未装饰的参数化类名称是非法的。显式特化形式可以表示特定参数或默认特化形式。类解析运算符可以访问作为类的本地参数或参数的值和类型参数。

示例：
```verilog
class C #(int p = 1);
    parameter int q = 5; // 本地参数
    static task t;
        int p;
        int x = C::p; // C::p 消除歧义  // C::p 不是默认特化中的 p
    endtask
endclass

int x = C::p; // 非法；在此上下文中不允许 C::
int y = C#()::p; // 合法；引用 C 的默认特化中的参数 p
typedef C T; // T 是默认特化，不是别名
int z = T::p; // 合法；T::p 引用默认特化中的 p
int v = C#(3)::p; // 合法；引用 C#(3) 中的参数 p
int w = C#()::q; // 合法；引用本地参数
T obj = new();
int u = obj.q; // 合法；引用本地参数
bit arr[obj.q]; // 非法：本地参数不是常量表达式
```

在参数化类方法的块外声明上下文中，使用类作用域解析运算符应该是对类内部的名称的引用，就好像在参数化类内部引用一样；不暗示特化。

示例：
```verilog
class C #(int p = 1, type T = int);
    extern static function T f();
endclass

function C::T C::f();
    return p + C::p;
endfunction

initial $display("%0d %0d", C#()::f(),C#(5)::f()); // 输出是 "2 10"
```

## 8.26 接口类
可以创建一组类，这些类可以被视为都具有一组共同的行为。这样的一组共同的行为可以使用 *接口类* 来创建。接口类使得相关类不需要共享一个公共的抽象超类，或者超类需要包含所有子类所需的所有方法定义。非接口类可以声明为实现一个或多个接口类。这为非接口类提供了一组方法定义，这些方法定义应满足虚方法覆盖的要求（参见 8.20）。

`interface class` 只能包含纯虚方法（参见 8.21）、类型声明（参见 6.18）和参数声明（参见 6.20，8.25）。约束块、覆盖组和嵌套类（参见 8.23）不允许在接口类中。接口类不得嵌套在另一个类中。接口类可以通过 `extends` 关键字继承一个或多个接口类，这意味着它继承了它扩展的接口类的所有成员类型、纯虚方法和参数，除了它可能隐藏的任何成员类型和参数。在多重继承的情况下，可能会发生名称冲突，必须解决（参见 8.26.6）。

类可以通过 `implements` 关键字实现一个或多个接口类。通过 `implements` 关键字实现的接口类不继承任何成员类型或参数。子类隐式实现其超类实现的所有接口类。在下面的示例中，类 C 隐式实现接口类 A，并具有所有要求和功能，就好像它显式实现接口类 A 一样：
```verilog
interface class A;
endclass

class B implements A;
endclass

class C extends B;
endclass
```

接口类的每个纯虚方法应该有一个虚方法实现，以便被非抽象类实现。当接口类由类实现时，接口类方法的必需实现可以由继承的虚方法实现提供。`virtual class` 应该为每个实现的 `virtual class` 的纯虚方法原型或虚方法实现定义或继承。应使用关键字 `virtual`，除非继承了虚方法。

变量的声明类型为接口类类型时，其声明类型的值可以是实现指定接口类的任何类的实例的引用（参见 8.22）。仅仅因为一个类为接口类的所有纯虚方法提供了实现并不足够；该类或其一个超类应该通过 `implements` 关键字声明为实现接口类，否则该类不实现接口类。

以下是接口类的简单示例。
```verilog
interface class PutImp#(type PUT_T = logic);
    pure virtual function void put(PUT_T a);
endclass

interface class GetImp#(type GET_T = logic);
    pure virtual function GET_T get();
endclass
class Fifo#(type T = logic, int DEPTH=1) implements PutImp#(T), GetImp#(T);
    T myFifo [$:DEPTH-1];
    virtual function void put(T a);
        myFifo.push_back(a);
    endfunction
    virtual function T get();
        get = myFifo.pop_front();
    endfunction
endclass

class Stack#(type T = logic, int DEPTH=1) implements PutImp#(T), GetImp#(T);
    T myFifo [$:DEPTH-1];
    virtual function void put(T a);
        myFifo.push_front(a);
    endfunction
    virtual function T get();
        get = myFifo.pop_front();
    endfunction
endclass
```

例子中有两个接口类 PutImp 和 GetImp，它们包含原型纯虚方法 put 和 get。Fifo 和 Stack 类使用关键字 `implements` 来实现 PutImp 和 GetImp 接口类，并为 put 和 get 提供实现。这些类因此共享共同的行为，而不共享共同的实现。

### 8.26.1 接口类语法
---
```verilog
interface_class_declaration ::= // from A.1.2
interface class class_identifier [ parameter_port_list ] 
[ extends interface_class_type { , interface_class_type } ] ;
{ interface_class_item } 
endclass [ : class_identifier] 
interface_class_item ::= 
type_declaration 
| { attribute_instance } interface_class_method 
| local_parameter_declaration ;
| parameter_declaration7 ;
| ;
interface_class_method ::= 
pure virtual method_prototype ;
// 7) 在作为 class_item 的 parameter_declaration 中，parameter 关键字应当是 localparam 关键字的同义词。
```
---
语法 8-3 接口类语法（摘自附录 A）

### 8.26.2 extends 对比 implements
概念上，`extends` 是一种机制，用于向超类添加或修改行为，而 `implements` 是要求为接口类中的纯虚方法提供实现。当一个类被扩展时，类的所有成员都被继承到子类中。当一个接口类被实现时，没有任何成员被继承。

接口类可以扩展，但不实现，一个或多个接口类，这意味着接口子类从多个接口类中继承成员，并可以添加额外的成员类型、纯虚方法原型和参数。一个类或虚类可以实现，但不扩展，一个或多个接口类。因为虚类是抽象的，它不需要完全定义来实现其实现类的方法（参见 8.26.7）。以下是这些区别的重点：
 - 一个接口类
   - 可以扩展零个或多个接口类
   - 不能实现接口类
   - 不能扩展类或虚类
   - 不能实现类或虚类
 - 一个类或虚类
   - 不能扩展接口类
   - 可以实现零个或多个接口类
   - 最多可以扩展一个其他类或虚类
   - 不能实现类或虚类
   - 可以同时扩展一个类和实现接口类

在下面的示例中，一个类既扩展一个基类，又实现两个接口类：
```verilog
interface class PutImp#(type PUT_T = logic);
    pure virtual function void put(PUT_T a);
endclass

interface class GetImp#(type GET_T = logic);
    pure virtual function GET_T get();
endclass

class MyQueue #(type T = logic, int DEPTH = 1);
    T PipeQueue[$:DEPTH-1];
    virtual function void deleteQ();
        PipeQueue.delete();
    endfunction
endclass

class Fifo #(type T = logic, int DEPTH = 1)
    extends MyQueue#(T, DEPTH)
    implements PutImp#(T), GetImp#(T);
    virtual function void put(T a);
        PipeQueue.push_back(a);
    endfunction
    virtual function T get();
        get = PipeQueue.pop_front();
    endfunction
endclass
```

在这个例子中，PipeQueue 属性和 deleteQ 方法被 Fifo 类继承。此外，Fifo 类还实现了 PutImp 和 GetImp 接口类，因此应为 put 和 get 方法提供实现。

下面的示例演示了多个类型可以在类定义中进行参数化，并且解析的类型用于实现的 PutImp 和 GetImp 接口类。
```verilog
virtual class XFifo#(type T_in = logic, type T_out = logic, int DEPTH = 1)
                     extends MyQueue#(T_out)
                     implements PutImp#(T_in), GetImp#(T_out);
    pure virtual function T_out translate(T_in a);
    virtual function void put(T_in a);
        PipeQueue.push_back(translate(a));
    endfunction
    virtual function T_out get();
        get = PipeQueue.pop_front();
    endfunction
endclass
```

继承的虚方法可以为实现的接口类的方法提供实现。下面是一个例子：
```verilog
interface class IntfClass;
    pure virtual function bit funcBase();
    pure virtual function bit funcExt();
endclass

class BaseClass;
    virtual function bit funcBase();
        return (1);
    endfunction
endclass

class ExtClass extends BaseClass implements IntfClass;
    virtual function bit funcExt();
        return (0);
    endfunction
endclass
```

ExtClass 通过提供 funcExt 的实现来实现 IntfClass 的要求，并通过从 BaseClass 继承 funcBase 的实现来实现 IntfClass 的要求。

非虚方法不提供对实现的接口类方法的实现。
```verilog
interface class IntfClass;
    pure virtual function void f();
endclass

class BaseClass;
    function void f();
        $display("Called BaseClass::f()");
    endfunction
endclass

class ExtClass extends BaseClass implements IntfClass;
    virtual function void f();
        $display("Called ExtClass::f()");
    endfunction
endclass
```

BaseClass 中的非虚函数 f() 不满足实现 IntfClass 的要求。ExtClass 中 f() 的实现同时隐藏了 BaseClass 中的 f() 并满足实现 IntfClass 的要求。

### 8.26.3 类型访问
接口类中的参数和 typedef 通过扩展的接口类继承，但不通过实现的接口类继承。参数和 typedef 在接口类中是静态的，并且可以通过类作用域解析运算符 :: （见 8.23）访问。不能通过接口类选择（点引用）访问接口类参数。

例1：类型和参数声明通过 extends 继承
```verilog
interface class IntfA #(type T1 = logic);
    typedef T1[1:0] T2;
    pure virtual function T2 funcA();
endclass : IntfA

interface class IntfB #(type T = bit) extends IntfA #(T);
    pure virtual function T2 funcB(); // 合法，类型 T2 被继承
endclass : IntfB
```

例2：类型和参数声明不通过 implements 继承，必须使用类作用域解析运算符
```verilog
interface class IntfC;
    typedef enum {ONE, TWO, THREE} t1_t;
    pure virtual function t1_t funcC();
endclass : IntfC

class ClassA implements IntfC;
    t1_t t1_i; // 错误，t1_t 没有从 IntfC 继承
    virtual function IntfC::t1_t funcC(); // 正确
        return (IntfC::ONE); // 正确
    endfunction : funcC
endclass : ClassA
```

### 8.26.4 类型使用限制
类不能实现类型参数，接口类也不能扩展类型参数，即使类型参数解析为接口类。以下例子说明了这一限制，并且是非法的：
```verilog
class Fifo #(type T = PutImp) implements T;
virtual class Fifo #(type T = PutImp) implements T;
interface class Fifo #(type T = PutImp) extends T;
```

类不能为接口类实现前向类型定义。接口类不能从接口类的前向类型定义扩展。接口类必须在实现或扩展之前声明。
```verilog
typedef interface class IntfD;

class ClassB implements IntfD #(bit); // 非法
    virtual function bit[1:0] funcD();
endclass : ClassB

// 接口类声明必须在 ClassB 之前
interface class IntfD #(type T1 = logic);
    typedef T1[1:0] T2;
    pure virtual function T2 funcD();
endclass : IntfD
```

### 8.26.5 类型转换和对象引用赋值
把对象句柄赋值给对象实现的接口类类型变量是合法的。
```verilog
class Fifo #(type T = int) implements PutImp#(T), GetImp#(T);
endclass
Fifo#(int) fifo_obj = new;
PutImp#(int) put_ref = fifo_obj;
```

在接口类变量之间动态类型转换是合法的，如果实际类句柄对于要赋值的目标是合法的。
```verilog
GetImp#(int) get_ref;
Fifo#(int) fifo_obj = new;
PutImp#(int) put_ref = fifo_obj;
$cast(get_ref, put_ref);
```

在上面的例子中，put_ref 是一个实现 GetImp#(int) 的 Fifo#(int) 实例。从对象句柄到接口类类型句柄的转换也是合法的。
```verilog
$cast(fifo_obj, put_ref); // 合法
$cast(put_ref, fifo_obj); // 合法，但不需要转换
```

与抽象类一样，接口类类型的对象不应该被构造。
```verilog
put_ref = new(); // 非法
```

从空源接口类句柄进行转换的处理方式与从空源类句柄进行转换的处理方式相同（参见 8.16）。

### 8.26.6 名称冲突和解决
当一个类实现多个接口类时，或者一个接口类扩展多个接口类时，来自不同名称空间的标识符被合并到一个单一的名称空间中。当这种情况发生时，可能会同时在单一名称空间中看到来自多个名称空间的相同标识符，从而创建一个必须解决的名称冲突。

#### 8.26.6.1 方法名称冲突解决
可能存在一个接口类继承多个方法，或者一个类被要求通过 `implements` 提供多个方法的实现，这些方法具有相同的名称。这是一个方法名称冲突。方法名称冲突应该通过一个单一的方法原型或实现来解决，同时为所有具有相同名称的纯虚方法提供一个实现。该方法原型或实现还必须是任何同名继承方法的有效虚方法覆盖。

例如：
```verilog
interface class IntfBase1;
    pure virtual function bit funcBase();
endclass

interface class IntfBase2;
    pure virtual function bit funcBase();
endclass

virtual class ClassBase;
    pure virtual function bit funcBase();
endclass

class ClassExt extends ClassBase implements IntfBase1, IntfBase2;
    virtual function bit funcBase();
        return (0);
    endfunction
endclass
```

类 ClassExt 提供了 funcBase 的实现，覆盖了来自 ClassBase 的纯虚方法原型，同时为来自 IntfBase1 和 IntfBase2 的 funcBase 提供实现。

也有方法名称冲突不能解决的情况。

例如：

```verilog
interface class IntfBaseA;
    pure virtual function bit funcBase();
endclass

interface class IntfBaseB;
    pure virtual function string funcBase();
endclass

class ClassA implements IntfBaseA, IntfBaseB;
    virtual function bit funcBase();
        return (0);
    endfunction
endclass
```

在这个情况下，funcBase 在 IntfBaseA 和 IntfBaseB 中都定义原型，但是有不同的返回类型 bit 和 string。尽管 funcBase 的实现是一个 IntfBaseA::funcBase 的合法覆盖，但是不同时是 IntfBaseB::funcBase 原型的合法覆盖，所以报错。

#### 8.26.6.2 参数和类型声明冲突和解决
接口类可以从多个接口类继承参数和类型声明。如果从不同的接口类继承了相同的名称，则会发生名称冲突。子类应该提供参数和/或类型声明，覆盖所有这样的名称冲突。

例如：
```verilog
interface class PutImp#(type T = logic);
    pure virtual function void put(T a);
endclass

interface class GetImp#(type T = logic);
    pure virtual function T get();
endclass

interface class PutGetIntf#(type TYPE = logic)
    extends PutImp#(TYPE), GetImp#(TYPE);
    typedef TYPE T;
endclass
```

在上面的示例中，参数 T 继承自 PutImp 和 GetImp。尽管 PutImp::T 与 GetImp::T 匹配，但仍会发生冲突，并且 PutGetIntf 从未使用过冲突。PutGetIntf 用类型定义覆盖 T 以解决冲突。

#### 8.26.6.3 菱形关系
如果接口类由相同的类实现或由相同的接口类以多种方式继承，则会出现 *菱形关系*。在菱形关系的情况下，为了避免名称冲突，将只合并来自任何单个接口类的符号的一个副本。例如:
```verilog
interface class IntfBase;
    parameter SIZE = 64;
endclass

interface class IntfExt1 extends IntfBase;
    pure virtual function bit funcExt1();
endclass

interface class IntfExt2 extends IntfBase;
    pure virtual function bit funcExt2();
endclass

interface class IntfExt3 extends IntfExt1, IntfExt2;
endclass
```

在上面的例子中，类 IntfExt3 继承了来自 IntfExt1 和 IntfExt2 的参数 SIZE。由于这些参数来自同一个接口类 IntfBase，因此只有一个 SIZE 的副本可以继承到 IntfExt3 中，因此不应将其视为冲突。

参数化接口类的每个唯一参数化都是接口类专门化。每个接口类专门化都被认为是唯一的接口类类型。因此，如果同一参数化接口类的不同专门化由同一接口类继承或由同一类实现，则不存在菱形关系。因此，可能会发生 8.26.6.1 中描述的方法名称冲突以及 8.26.6.2 中描述的参数和类型声明名称冲突。例如:
```verilog
interface class IntfBase #(type T = int);
    pure virtual function bit funcBase();
endclass

interface class IntfExt1 extends IntfBase#(bit);
    pure virtual function bit funcExt1();
endclass

interface class IntfExt2 extends IntfBase#(logic);
    pure virtual function bit funcExt2();
endclass

interface class IntfFinal extends IntfExt1, IntfExt2;
    typedef bit T; // 覆盖冲突的标识符名称
    pure virtual function bit funcBase();
endclass
```

在前面的示例中，接口类 IntfBase 有两种不同的参数化。IntfBase 的每一个参数化都是一个专门化；因此不存在菱形关系，并且必须解决参数 T 和方法 funcBase 之间的冲突。

### 8.26.7 部分实现
可以创建未完全定义的类，并通过使用虚类来利用接口类（见8.21）。因为虚类不必完全定义它们的实现，所以它们可以自由地部分定义它们的方法。下面是一个部分实现的虚拟类的例子。
```verilog
interface class IntfClass;
    pure virtual function bit funcA();
    pure virtual function bit funcB();
endclass

// 部分实现 IntfClass
virtual class ClassA implements IntfClass;
    virtual function bit funcA();
        return (1);
    endfunction
    pure virtual function bit funcB();
endclass

// 完全实现 IntfClass
class ClassB extends ClassA;
    virtual function bit funcB();
        return (1);
    endfunction
endclass
```

在不满足接口类原型要求的情况下，使用接口类部分定义虚类是违法的。换句话说，当接口类由虚类实现时，虚类必须为每个接口类的方法原型执行以下操作之一：
 - 提供方法实现
 - 用 pure 限定符重新声明方法原型

在前面的例子中，ClassA 完全定义了 funcA，但是重新声明了原型 funcB。

### 8.26.8 方法默认参数值
接口类中的方法声明可以有默认的参数值。默认表达式应该是一个常量表达式，并在包含子例程声明的作用域中求值。对于实现该方法的所有类，常量表达式的值应该是相同的。更多信息请参见13.5.3。

### 8.26.9 约束块、覆盖组和随机化
约束块和覆盖组不能在接口类中声明。

随机方法调用对于接口类句柄应该是合法的。虽然内联约束也是合法的，但接口类不能包含任何数据，这意味着内联约束只能表示与状态变量相关的条件，因此效用非常有限。由于名称解析规则和接口类不允许包含数据成员的事实，使用 rand_mode 和 constraint_mode 不应该是合法的。

接口类包含两个内置的空虚拟方法 pre_randomize() 和 post_randomize()，它们在随机化之前和之后自动调用。这些方法可以被重写。作为一种特殊情况，pre_randomize() 和 post_randomize() 不会导致方法名冲突。

## 8.27 typedef 类
有时需要在声明类本身之前声明类变量；例如，如果两个类都需要彼此的句柄。当编译器在处理第一个类的声明过程中遇到对第二个类的引用时，该引用是未定义的，并且编译器将其标记为错误。

这可以通过使用 `typedef` 为第二个类提供前向声明来解决：
```verilog
typedef class C2; // C2 被声明为 class 类型
class C1; 
    C2 c;
endclass

class C2; 
    C1 c;
endclass
```

在本例中，C2 被声明为 class 类型，这一事实在后面的源代码中得到了加强。class 构造总是创建类型，而不需要为此目的声明 typedef（如 typedef class…）。

在前面的例子中，语句中的 `class` 关键字 `typedef class C2;` 不是必需的，仅用于文档目的。语句 `typedef C2;` 是相等的，应该以同样的方式工作。

与 6.18 中描述的其他前向类型一样，前向类声明的实际类定义应在相同的局部作用域或生成块中解析。

类的前向 `typedef` 可以引用带有参数端口列表的类。

例子:
```verilog
typedef class C ;
module top ;
    C#(1, real) v2 ; // 位置参数覆盖
    C#(.p(2), .T(real)) v3 ; // 命名参数覆盖
endmodule

class C #(parameter p = 2, type T = int);
endclass
```

## 8.28 类和结构
从表面上看，似乎 class 和 struct 提供了相同的功能，并且只需要其中一个。然而，事实并非如此；class 与 struct 在以下三个基本方面有所不同：
 - a) SystemVerilog 结构体是严格的静态对象；它们要么在静态内存位置（全局或模块作用域）中创建，要么在自动任务的堆栈中创建。相反，SystemVerilog 对象（即类实例）完全是动态的；它们的声明并不创建对象。创建对象是通过调用 new 来完成的。
 - b) SystemVerilog 对象使用句柄实现，从而提供类似 C 语言的指针功能。但是 SystemVerilog 不允许将句柄转换到其他数据类型；因此，SystemVerilog 句柄没有与 C 指针相关的风险。
 - c) SystemVerilog 对象构成了提供真正多态性的面向对象数据抽象的基础。类继承、抽象类和动态强制转换是功能强大的机制，它们远远超出了结构提供的单纯封装机制。

## 8.29 内存管理
对象、字符串、动态数组和关联数组的内存是动态分配的。创建对象时，SystemVerilog 分配更多内存。当一个对象不再需要时，SystemVerilog 自动回收内存，使其可重用。自动内存管理系统是 SystemVerilog 的一个组成部分。如果没有自动内存管理，SystemVerilog 的多线程、可重入环境会给用户带来很多问题。手动内存管理系统，例如 C 语言的 malloc 和 free 提供的系统，是不够的。

考虑下面的例子：
```verilog
myClass obj = new;
fork
    task1( obj );
    task2( obj );
join_none
```

在本例中，主进程（分离两个任务的进程）不知道何时可以使用对象 obj 完成这两个进程。同样，task1 和 task2 都不知道其他两个进程何时不再使用对象 obj。从这个简单的示例中可以明显看出，没有一个进程拥有足够的信息来确定何时释放对象是安全的。只有以下两个选项可供用户选择：
 - 小心行事，永远不要收回对象，或者
 - 添加某种形式的引用计数，可用于确定何时可以安全回收对象。

采用第一个选项可能会导致系统很快耗尽内存。第二种选择给用户带来了很大的负担，他们除了管理测试平台之外，还必须使用不太理想的模式来管理内存。为了避免这些缺点，SystemVerilog 自动管理所有动态内存。

用户不需要担心悬空引用、过早回收或内存泄漏。系统将自动回收不再使用的物品。在前面的示例中，用户所做的就是在不再需要 obj 句柄时，将所有引用它的变量赋值为 null。当一个对象在任何活动作用域中存在对该对象的未完成引用，或者对该对象的非静态成员的未完成的非阻塞赋值时，该对象不得被回收。
