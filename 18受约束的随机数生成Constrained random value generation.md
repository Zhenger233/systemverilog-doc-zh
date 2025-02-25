# 18. 受约束的随机数生成
## 18.1 概述
本章描述以下内容：
 - 随机变量
 - 约束块
 - 随机化方法
 - 禁用随机化
 - 控制约束
 - 作用域变量随机化
 - 给随机数生成器（RNG）设置种子
 - 随机加权 case 语句
 - 随机序列生成

## 18.2 总览
约束驱动的测试生成允许用户自动生成功能验证测试。随机测试可能比传统的有针对性的测试方法更有效。通过指定约束，可以轻松创建可以找到难以到达的边界情况的测试。SystemVerilog 允许用户以一种紧凑的声明方式指定约束。然后，约束由求解器处理，生成满足约束的随机值。

随机约束通常在面向对象数据抽象之上指定，模拟要随机化的数据为包含随机变量和用户定义约束的对象。约束确定可以分配给随机变量的合法值。对象非常适合表示复杂的聚合数据类型和协议，例如以太网数据包。

章节 18.3 提供了基于对象的随机化和约束编程的概述。本章的其余部分提供了有关随机变量、约束块和用于操作它们的机制的详细信息。

## 18.3 概念和用法
本小节介绍了在对象中生成随机激励的基本概念和用法。SystemVerilog 使用面向对象的方法为对象的成员变量分配随机值，受用户定义的约束限制。例如：
```verilog
class Bus;
    rand bit[15:0] addr;
    rand bit[31:0] data;

    constraint word_align {addr[1:0] == 2'b0;}
endclass
```

Bus 类模拟了一个简化的总线，其中包含两个随机变量 addr 和 data，分别表示总线上的地址和数据值。word_align 约束声明了 addr 的随机值必须是字对齐的（低位 2 位为 0）。

调用 randomize() 方法会为总线对象生成新的随机值：
```verilog
Bus bus = new;

repeat (50) begin
    if ( bus.randomize() == 1 )
        $display ("addr = %16h data = %h\n", bus.addr, bus.data);
    else
        $display ("Randomization failed.\n");
end
```

调用 randomize() 会为对象的所有随机变量选择新的值，以使所有约束为真（满足）。在上面的程序测试中，创建了一个 bus 对象，然后随机化 50 次。检查每次随机化的结果是否成功。如果随机化成功，则打印 addr 和 data 的新随机值；如果随机化失败，则打印错误消息。在此示例中，只约束了 addr 值，而 data 值是无约束的。无约束的变量会被分配其声明范围内的任何值。

约束编程是一种强大的方法，允许用户构建通用、可重用的对象，稍后可以扩展或约束以执行特定功能。该方法与传统的过程式和面向对象编程都不同，如下面的示例所示，该示例扩展了 Bus 类：
```verilog
typedef enum {low, mid, high} AddrType;

class MyBus extends Bus;
    rand AddrType atype;

    constraint addr_range
    {
        (atype == low ) -> addr inside { [0 : 15] };
        (atype == mid ) -> addr inside { [16 : 127]};
        (atype == high) -> addr inside {[128 : 255]};
    }
endclass
```

MyBus 类继承了 Bus 类的所有随机变量和约束，并添加了一个名为 atype 的随机变量，用于使用另一个约束控制地址范围。addr_range 约束使用蕴含来根据 atype 的随机值选择三个范围约束中的一个。当随机化 MyBus 对象时，将计算 addr、data 和 atype 的值，以使所有约束都得到满足。使用继承构建分层约束系统使得能够开发通用模型，可以约束以执行特定应用程序功能。

可以使用 randomize() `with` 构造进一步约束对象。该构造在调用 randomize() 时内联声明附加约束：
```verilog
task exercise_bus (MyBus bus);
    int res;

    // 示例 1：限制为低地址
    res = bus.randomize() with {atype == low;};

    // 示例 2：限制地址在 10 到 20 之间
    res = bus.randomize() with {10 <= addr && addr <= 20;};

    // 示例 3：将数据值限制为 2 的幂
    res = bus.randomize() with {(data & (data - 1)) == 0;};
endtask
```

此示例说明了约束的几个重要属性，如下所示：
 - 约束可以是任何 SystemVerilog 整数类型（例如 `bit`、`reg`、`logic`、`integer`、`enum`、`packed struct`）的变量和常量组成的表达式。
 - 约束求解器应能够处理各种方程，例如代数因式分解、复杂的布尔表达式和混合整数和位表达式。在上面的示例中，2 的幂约束是用算术表达的。也可以使用移位运算符定义表达式；例如，1 << n，其中 n 是一个 5 位随机变量。
 - 如果存在解，则约束求解器将找到解。只有在问题过度约束且没有组合满足约束的随机值时，求解器才会失败。
 - 约束双向交互。在此示例中，为 addr 选择的值取决于 atype 及其如何约束，为 atype 选择的值取决于 addr 及其如何约束。所有表达式运算符都是双向处理的，包括蕴含运算符（`->`）。
 - 约束仅支持 2 状态值。4 状态值（X 或 Z）或 4 状态运算符（例如，`===`、`!==`）是非法的，将导致错误。

有时，禁用随机变量的约束是有用的。例如，为了故意生成非法地址（非字对齐）：
```verilog
task exercise_illegal(MyBus bus, int cycles);
    int res;

    // 禁用字对齐约束。
    bus.word_align.constraint_mode(0);

    repeat (cycles) begin
        // CASE 1：限制为小地址。
        res = bus.randomize() with {addr[0] || addr[1];};
        ...
    end

    // 重新启用字对齐约束
    bus.word_align.constraint_mode(1);
endtask
```

constraint_mode() 方法可用于启用或禁用对象中的任何命名约束块。在此示例中，禁用了字对齐约束，然后使用额外约束强制低位地址位非零（因此不对齐）随机化对象。

启用或禁用约束的能力允许用户设计约束层次结构。在这些层次结构中，最低级约束可以表示由共同属性分组的物理限制，这些属性分组为命名约束块，可以独立启用或禁用。

类似地，rand_mode() 方法可用于启用或禁用任何随机变量。当禁用随机变量时，它的行为与其他非随机变量完全相同。

有时，希望在随机化之前或之后立即执行操作。这通过两个内置方法 pre_randomize() 和 post_randomize() 实现，这两个方法在随机化之前和之后自动调用。这些方法可以被覆盖以实现所需的功能：
```verilog
class XYPair;
    rand integer x, y;
endclass

class MyXYPair extends XYPair ;
    function void pre_randomize();
        super.pre_randomize(); 
        $display("Before randomize x=%0d, y=%0d", x, y);
    endfunction

    function void post_randomize();
        super.post_randomize();
        $display("After randomize x=%0d, y=%0d", x, y);
    endfunction
endclass
```

默认情况下，pre_randomize() 和 post_randomize() 调用它们被覆盖的基类的方法。当 pre_randomize() 或 post_randomize() 被重载，必须小心执行基类的方法，除非类是基类（没有基类）。否则，基类方法不应被调用。

随机激励生成的能力和面向对象基于约束的验证方法学使用户快速开发测试，覆盖复杂功能，更好保证设计正确性。

## 18.4 随机变量
可以使用 `rand` 和 `randc` 类型修饰符关键字声明类变量为随机。在类中声明随机变量的语法如下 8-1：
---
```verilog
class_property ::= // from A.1.9
{ property_qualifier } data_declaration 
property_qualifier8 ::= 
random_qualifier 
| class_item_qualifier 
random_qualifier8 ::= 
rand
| randc
// 8) 在任一声明中，只允许 protected 或 local 中的一个，只允许 rand 或 randc 中的一个，static 和/或 virtual 只能出现一次。
```
---
语法 18-1—随机变量声明语法（摘自附录 A）

 - 求解器可以随机化任何整数类型的单个变量。
 - 数组可以声明为 `rand` 或 `randc`，此时其所有成员元素都被视为 `rand` 或 `randc`。
 - 可以约束单个数组元素，此时索引表达式可能包括迭代约束循环变量、常量和状态变量。
 - 动态数组、关联数组和队列可以声明为 `rand` 或 `randc`。数组中的所有元素都被随机化，覆盖任何先前的数据。
 - 可以约束动态数组或队列的大小。在这种情况下，数组将根据大小约束调整大小，然后随机化所有数组元素。数组大小约束使用 size 方法声明。例如：
   ```verilog
   rand bit [7:0] len;
   rand integer data[];
   constraint db { data.size == len; }
   ```

   变量 len 被声明为 8 位宽。随机化器计算 len 变量的随机值，范围为 8 比特的 0 到 255，然后随机化 data 数组的前 len 个元素。
   
   当动态数组被随机化调整大小时，调整后的数组将被初始化（参见 7.5.1）为原始数组。当队列被随机化调整大小时，根据需要在队列的后面（即右侧）插入或删除元素（参见 7.10.2.2 和 7.10.2.3）以生成新的队列大小；插入的任何新元素都采用元素类型的默认值。也就是说，调整大小会增长或缩小数组。这对于类句柄的动态数组或队列很重要。随机化不会分配任何类对象。直到新大小，现有类对象被保留并且其内容被随机化。如果新大小大于原始大小，则每个附加元素都具有不需要随机化的 `null` 值。

   在通过随机化或 `new` 调整动态数组或队列的大小时，保留了每个保留元素的 rand_mode，并且每个新元素的 rand_mode 设置为 active。

   如果动态数组的大小没有约束，则数组不会被调整大小，所有数组元素都会被随机化。

 - 可以声明对象句柄为 `rand`，在这种情况下，该对象的所有变量和约束与包含该句柄的对象的变量和约束同时求解。随机化不会修改实际对象句柄。对象句柄不应声明为 `randc`。
 - 可以声明未打包结构为 `rand`，在这种情况下，该结构的所有随机成员使用本节中列出的规则同时求解。未打包结构不应声明为 `randc`。未打包结构的成员可以通过在其类型声明中使用 `rand` 或 `randc` 修饰符使其成为随机。包含联合的未打包结构的成员以及打包结构的成员不允许具有随机修饰符。

   例如：
   ```verilog
   class packet;
       typedef struct {
           randc int addr = 1 + constant;
           int crc;
           rand byte data [] = {1,2,3,4};
       } header;
       rand header h1;
   endclass
   packet p1=new;
   ```

### 18.4.1 Rand 修饰符
使用 `rand` 关键字声明的变量是标准随机变量。它们的值在其范围内均匀分布。例如：
```verilog
rand bit [7:0] y;
```

这是一个 8 位无符号整数，范围为 0 到 255。如果未约束，则该变量将被分配 0 到 255 范围内的任何值，概率相等。在此示例中，连续调用 randomize() 时相同值重复的概率为 1/256。

### 18.4.2 Randc 修饰符
使用 `randc` 关键字声明的变量是随机循环变量，它们在其声明范围的随机排列中循环。

为了理解 `randc`，考虑一个 2 位随机变量 y：
```verilog
randc bit [1:0] y;
```

变量 y 可以取值 0、1、2 和 3（范围为 0 到 3）。randomize() 计算 y 的范围值的初始随机排列，然后在连续调用中按顺序返回这些值。在返回排列的最后一个元素后，它会重复该过程，计算一个新的随机排列。

随机循环变量的基本思想是，`randc` 在范围内随机迭代所有值，并且在迭代中不重复任何值。当迭代完成后，新的迭代会自动开始（参见图 18-1）。
![eor](18-1.png)

图 18-1—`randc` 示例

对于任何给定的 `randc` 变量，当该变量的约束发生变化或者该变量的剩余值中没有一个可以满足约束时，求解器会重新计算该变量的随机排列。随机排列序列只能包含 2 状态值。

为了减少内存需求，实现可能对 `randc` 变量的最大大小施加限制，但不得少于 8 位。

随机循环变量的语义要求它们在其他随机变量之前解决。包含 `rand` 和 `randc` 变量的约束集应该这样解决，以便 `randc` 变量首先解决，这有时会导致 randomize() 失败。

如果随机变量声明为 `static`，则该变量的 randc 状态也应为静态。因此，当通过基类的任何实例随机化变量时，randomize 会选择下一个循环值（从单个序列中）。

## 18.5 约束块
使用约束表达式确定随机变量的值，约束表达式使用约束块声明。约束块是类成员，如任务、函数和变量。约束块名称在类中必须是唯一的。

声明约束块的语法如下 18-2：
---
```verilog
constraint_declaration ::= // from A.1.10
[ static ] constraint constraint_identifier constraint_block 
constraint_block ::= { { constraint_block_item } }
constraint_block_item ::= 
solve solve_before_list before solve_before_list ;
| constraint_expression 
solve_before_list ::= constraint_primary { , constraint_primary } 
constraint_primary ::= [ implicit_class_handle . | class_scope ] hierarchical_identifier select 
constraint_expression ::= 
[ soft ] expression_or_dist ;
| expression –> constraint_set 
| if ( expression ) constraint_set [ else constraint_set ] 
| foreach ( ps_or_hierarchical_array_identifier [ loop_variables ] ) constraint_set 
| disable soft constraint_primary ;
constraint_set ::= 
constraint_expression 
| { { constraint_expression } }
dist_list ::= dist_item { , dist_item } 
dist_item ::= value_range [ dist_weight ] 
dist_weight ::= 
:= expression 
| :/ expression 
constraint_prototype ::= [constraint_prototype_qualifier] [ static ] constraint constraint_identifier ;
constraint_prototype_qualifier ::= extern | pure
extern_constraint_declaration ::= 
[ static ] constraint class_scope constraint_identifier constraint_block 
identifier_list ::= identifier { , identifier } 
expression_or_dist ::= expression [ dist { dist_list } ] // from A.2.10
loop_variables ::= [ index_variable_identifier ] { , [ index_variable_identifier ] } // from A.6.8
```
---
语法 18-2—约束语法（摘自附录 A）

constraint_identifier 是约束块的名称。这个名称可以用来使用 constraint_mode() 方法启用或禁用约束（参见 18.9）。

constraint_block 是限制变量范围或定义变量之间关系的表达式语句列表。constraint_expression 是任何 SystemVerilog 表达式或约束特定运算符，如 `dist` 和 `->`（参见 18.5.4 和 18.5.6）。

约束的声明性质对约束表达式施加以下限制：
 - 函数允许，但有一定限制（参见 18.5.12）。
 - 具有副作用的运算符，例如 `++` 和 `--`，是不允许的。
 - 不能在顺序约束中指定 `randc` 变量（参见 18.5.10 中的 `solve...before`）。
 - `dist` 表达式不能出现在其他表达式中。

### 18.5.1 外部约束块
如果 *约束原型* 出现在类声明中，则可以在其封闭类声明之外声明约束块。约束原型指定类应具有指定名称的约束，但不指定实现该约束的约束块。约束原型可以采用两种形式，如下面的示例所示：
```verilog
class C;
    rand int x;
    constraint proto1; // 隐式形式
    extern constraint proto2; // 显式形式
endclass
```

对于这两种形式，可以通过使用类作用域解析运算符提供 *外部约束块* 来完成约束，如下例所示：
```verilog
constraint C::proto1 { x inside {-4, 5, 7}; }
constraint C::proto2 { x >= 0; }
```

外部约束块应出现在与相应类声明相同的作用域中，并且应在该作用域中的类声明之后出现。如果使用显式形式的约束原型，并且未提供相应的外部约束块，则如果没有提供相应的外部约束块，则应该是一个错误。如果使用隐式形式的原型，并且没有提供相应的外部约束块，则应将约束视为空约束，并可能发出警告。空约束是对随机化没有影响的约束，等效于包含常量表达式 1 的约束块。

对于任一形式，如果为任何给定原型提供了多个外部约束块，则应该是一个错误，如果在同一类声明中出现与原型同名的约束块，则应该是一个错误。

### 18.5.2 约束继承
约束遵循与其他类成员相同的一般继承规则。randomize() 方法是虚拟的，因此无论调用它的对象句柄的数据类型如何，它都会遵守调用该对象的约束。

派生类应继承其超类的所有约束。派生类中具有与其超类中的约束相同名称的约束将替换该名称的继承约束。派生类中具有与其超类中约束不同名称的约束将是附加约束。

如果派生类具有与其超类中约束原型相同名称的约束原型，则该约束原型将替换继承的约束。然后，派生类的约束原型的完成应遵循 18.5.1 中描述的规则。

可以在抽象类中（即使用 8.21 中描述的 `virtual class` 语法声明的类）中包含 *纯约束*。纯约束在语法上类似于约束原型，但使用 `pure` 关键字，如下例所示：
```verilog
virtual class D;
    pure constraint Test;
endclass
```

纯约束表示对任何非抽象派生类（即不是 `virtual` 的派生类）提供同名约束的义务。如果非抽象类没有提供其继承的每个纯约束的实现，则应该是一个错误。在非抽象类中声明纯约束应该是一个错误。

如果一个类包含一个纯约束，同时也有与其继承的同名约束块、约束原型或外部约束块，则应该是一个错误。但是，任何类（无论是否是抽象类）都可以包含与其继承的纯约束同名的约束块或约束原型；这样的约束将覆盖纯约束，并且对于该类及其任何派生类都是非纯约束。

从超类继承约束的抽象类可能具有与其继承的约束相同名称的纯约束。在这种情况下，派生虚拟类中的纯约束将替换继承的约束。

覆盖纯约束的约束可以在覆盖类的主体中使用约束块声明，也可以使用约束原型和外部约束块，如 18.5.1 中所述。

### 18.5.3 集合成员
约束支持整数值集合和集合成员运算符（如 11.4.13 中定义）。

在没有其他约束的情况下，所有值（单个值或值范围）都有相等的概率被 `inside` 运算符选择。

`inside` 运算符的否定形式表示表达式不在集合中：`!(expression inside {set})`。

例如：
```verilog
rand integer x, y, z;
constraint c1 {x inside {3, 5, [9:15], [24:32], [y:2*y], z};}

rand integer a, b, c;
constraint c2 {a inside {b, c};}

integer fives[4] = '{ 5, 10, 15, 20 };
rand integer v;
constraint c3 { v inside {fives}; }
```

在 SystemVerilog 中，`inside` 运算符是双向的；因此，上面的第二个示例等效于 `a == b || a == c`。

### 18.5.4 分布
除了集合成员，约束还支持加权值集合，称为 *分布*。分布具有两个属性：它们是集合成员的关系测试，它们指定结果的统计分布函数。

定义分布表达式的语法如下 18-3：
---
```verilog
constraint_expression ::= // from A.1.10
expression_or_dist ;
... 
dist_list ::= dist_item { , dist_item }
dist_item ::= value_range [ dist_weight ] 
dist_weight ::= 
:= expression 
| :/ expression 
expression_or_dist ::= expression [ dist { dist_list } ] // from A.2.10
```
---
语法 18-3—约束分布语法（摘自附录 A）

表达式可以是任何整数 SystemVerilog 表达式。

如果表达式的值包含在集合中，则分布运算符 `dist` 返回 true；否则，返回 false。

在没有其他约束的情况下，表达式匹配列表中任何值的概率与其指定的权重成比例。如果对某些表达式的约束导致这些表达式上的分布权重不可满足，则实现只需要满足约束。一个例外是权重为零，它被视为约束。

分布集合是一个逗号分隔的整数表达式和范围列表。可选地，列表中的每个项都可以有一个权重，使用 `:=` 或 `:/` 运算符指定。如果没有为项指定权重，则默认权重为 `:= 1`。权重可以是任何整数 SystemVerilog 表达式。

`:=` 运算符将指定权重分配给项，或者如果项是范围，则将权重分配给范围中的每个值。

`:/` 运算符将指定权重分配给项，或者如果项是范围，则将权重分配给整个范围。如果范围中有 n 个值，则每个值的权重为 `range_weight / n`。例如：
```verilog
x dist {100 := 1, 200 := 2, 300 := 5}
```

意味着 x 等于 100、200 或 300，权重比为 1-2-5。如果添加了一个额外约束，指定 x 不能为 200：
```verilog
x != 200;
x dist {100 := 1, 200 := 2, 300 := 5}
```

那么 x 等于 100 或 300，权重比为 1-5。

更容易考虑混合比率，如 1-2-5，而不是实际概率，因为混合比率不必规范化为 100%。将概率转换为混合比率很简单。

当权重应用于范围时，它们可以应用于范围中的每个值，或者应用于整个范围。例如：
```verilog
x dist { [100:102] := 1, 200 := 2, 300 := 5}
```

意味着 x 等于 100、101、102、200 或 300，权重比为 1-1-1-2-5，以及
```verilog
x dist { [100:102] :/ 1, 200 := 2, 300 := 5}
```

意味着 x 等于 100、101、102、200 或 300，权重比为 1/3-1/3-1/3-2-5。

总的来说，分布保证两个属性：集合成员和单调加权。换句话说，增加权重会增加选择这些值的可能性。

限制如下：
 - 不得将 `dist` 操作应用于 `randc` 变量。
 - `dist` 表达式要求表达式至少包含一个 `rand` 变量。

### 18.5.5 唯一性约束
可以使用 `unique` 约束来确保一组变量的值中没有两个变量具有相同的值。被约束的变量组应当使用 `open_range_list` 语法指定，其中每个项都是以下之一：
 - 整数类型的标量变量
 - 其叶元素类型为整数的未打包数组变量，或这样一个变量的切片

---
```verilog
constraint_expression ::= // from A.1.10
... 
| uniqueness_constraint ;
uniqueness_constraint ::= 
unique { open_range_list9 }
// 9) uniqueness_constraint 中的 open_range_list 只能包含表示标量或数组变量的表达式，如 18.5.5 中所述。
```
---
语法 18-4—唯一性约束语法（摘自附录 A）

未打包数组的 *叶子元素* 通过向下遍历数组找到，直到找到一个不是未打包数组类型的元素。

所有指定的变量组成员（即任何标量变量和任何数组或切片的所有叶子元素）必须是等效类型。变量组中不得出现 `randc` 变量。

如果指定的变量组成员少于两个，则约束不起作用，不会导致约束冲突。

在下面的示例中，变量 `a[2]`、`a[3]`、b 和 excluded 在随机化后都将包含不同的值。由于约束 exclusion，变量 `a[2]`、`a[3]` 和 b 都不会包含值 5。
```verilog
rand byte a[5];
rand byte b;
rand byte excluded;
constraint u { unique {b, a[2:3], excluded}; }
constraint exclusion { excluded == 5; }
```

### 18.5.6 蕴含
约束提供了两个用于声明条件（谓词）关系的构造：蕴含和 `if-else`。

蕴含运算符（`->`）可用于声明蕴含约束表达式。

定义蕴含约束的语法如下 18-5：
---
```verilog
constraint_expression ::= // from A.1.10
... 
| expression –> constraint_set 
```
---
语法 18-5—约束蕴含语法（摘自附录 A）

expression 可以是任何整数 SystemVerilog 表达式。

蕴含运算符 `a -> b` 的布尔等价形式是 `!a || b`。这表示如果表达式为真，则生成的随机数受约束（或约束集）约束。否则，生成的随机数是无约束的。

constraint_set 表示任何有效的约束或未命名的约束集。如果表达式为真，则约束集中的所有约束也应满足。

例如：
```verilog
mode == little -> len < 10;
mode == big -> len > 100;
```

在此示例中，mode 的值意味着 len 的值应受到小于 10（mode == little）、大于 100（mode == big）或无约束（mode != little 和 mode != big）的约束。

在示例
```verilog
bit [3:0] a, b;
constraint c { (a == 0) -> (b == 1); }
```

a 和 b 都是 4 位；因此，a 和 b 有 256 种组合。约束 c 表示 `a == 0` 意味着 `b == 1`，从而消除了 15 种组合：`{0,0}、{0,2}、… {0,15}`。因此，`a == 0` 的概率为 `1/(256-15)` 或 `1/241`。

### 18.5.7 if-else 约束
`if-else` 约束也是支持的。

定义 `if-else` 约束的语法如下 18-6：
---
```verilog
constraint_expression ::= // from A.1.10
... 
| if ( expression ) constraint_set [ else constraint_set ] 
```
---
语法 18-6—If-else 约束语法（摘自附录 A）

expression 可以是任何整数 SystemVerilog 表达式。

constraint_set 表示任何有效的约束或未命名的约束集。如果表达式为真，则应满足第一个约束或约束集；否则，应满足可选 `else` 约束或约束集。约束集可用于组合多个约束。

`if-else` 风格约束声明等效于蕴含
```verilog
if (mode == little)
    len < 10;
else if (mode == big)
    len > 100;
```

等效于
```verilog
mode == little -> len < 10 ;
mode == big -> len > 100 ;
```

在此示例中，mode 的值意味着 len 的值应受到小于 10（mode == little）、大于 100（mode == big）或无约束（mode != little 和 mode != big）的约束。

与蕴含一样，`if-else` 风格约束是双向的。在前面的声明中，mode 的值约束 len 的值，len 的值约束 mode 的值。

因为 `if-else` 约束声明中的 `else` 部分是可选的，所以在嵌套的 `if` 序列中省略 `else` 时可能会引起混淆。这通过总是将 `else` 与最近的前一个缺少 `else` 的 `if` 关联来解决。在下面的示例中，`else` 与内部 `if` 关联，如缩进所示：
```verilog
if (mode != big) 
    if (mode == little)
        len < 10;
    else // else 应用于前面的 if
        len > 100;
```

### 18.5.8 迭代约束
迭代约束允许数组类变量使用循环变量和索引表达式随机化，或者使用数组缩减方法。

#### 18.5.8.1 foreach 迭代约束
定义 `foreach` 迭代约束的语法如下 18-7：
---
```verilog
constraint_expression ::= // from A.1.10
... 
| foreach ( ps_or_hierarchical_array_identifier [ loop_variables ] ) constraint_set 
loop_variables ::= [ index_variable_identifier ] { , [ index_variable_identifier ] } // from A.6.8
```
---
语法 18-7—Foreach 迭代约束语法（摘自附录 A）

`foreach` 构造指定对数组元素的迭代。其参数是一个标识符，指定任何类型的数组（固定大小、动态、关联或队列），后跟一个方括号括起来的循环变量列表。每个循环变量对应数组的一个维度。

例如：
```verilog
class C;
    rand byte A[] ;
    constraint C1 { foreach ( A [ i ] ) A[i] inside {2,4,8,16}; }
    constraint C2 { foreach ( A [ j ] ) A[j] > 2 * j; }
endclass
```

C1 约束数组 A 的每个元素在集合 `[2,4,8,16]` 中。C2 约束数组 A 的每个元素大于其索引的两倍。

循环变量的数量不得超过数组变量的维数。每个循环变量的作用域是 `foreach` 约束构造，包括其 constraint_set。每个循环变量的类型隐式声明为与数组索引的类型一致。空循环变量表示不迭代数组的该维度。与默认参数一样，末尾的逗号列表可以省略；因此，`foreach( arr [ j ] )` 是 `foreach( arr [ j, , , , ] )` 的简写。任何循环变量具有与数组相同的标识符应该是一个错误。

循环变量到数组索引的映射由维度基数确定，如 20.7 中所述。
```verilog
//     1  2  3         3    4       1   2   -> 维度编号
int A [2][3][4]; bit [3:0][2:1] B [5:1][4];

foreach( A [ i, j, k ] ) ...
foreach( B [ q, r, , s ] ) ...
```

第一个 `foreach` 使 i 从 0 到 1，j 从 0 到 2，k 从 0 到 3。第二个 `foreach` 使 q 从 5 到 1，r 从 0 到 3，s 从 2 到 1。

`foreach` 迭代约束可以包含谓词。例如：
```verilog
class C;
    rand int A[] ;
    constraint c1 { A.size inside {[1:10]}; }
    constraint c2 { foreach ( A[ k ] ) (k < A.size - 1) -> A[k + 1] > A[k]; }
endclass
```

第一个约束 c1 限制数组 A 的大小在 1 到 10 之间。第二个约束 c2 限制每个数组值大于其前一个值，即按升序排序的数组。

在 `foreach` 中，涉及只包含常量、状态变量、对象句柄比较、循环变量或正在迭代的数组大小的谓词表达式作为约束的保护，而不是逻辑关系。例如，约束 c2 中的蕴含涉及循环变量和正在迭代的数组大小；因此，只有当 k < A.size() - 1 时才允许创建约束，这种情况下防止了约束中的越界访问。保护在 18.5.13 中有更详细的描述。

索引表达式可以包含循环变量、常量和状态变量。无效或越界的数组索引不会自动消除；用户必须使用谓词显式排除这些索引。

动态数组或队列的 size 方法可用于约束数组的大小（参见约束 c1）。如果数组同时受大小约束和迭代约束约束，则首先解决大小约束，然后解决迭代约束。由于大小约束和迭代约束之间的隐式顺序，size 方法应在相应数组的 `foreach` 块中视为状态变量。例如，约束 c1 中的表达式 A.size 在约束 c1 中被视为随机变量，在约束 c2 中被视为状态变量。这种隐式顺序在某些情况下可能导致求解器失败。

#### 18.5.8.2 数组缩减迭代约束
数组缩减方法可以从整数数组中生成单个整数值（参见 7.12.3）。在约束的上下文中，数组缩减方法被视为一个表达式，对数组的每个元素进行迭代，使用每种方法的相关操作数连接。结果返回与数组元素类型相同的单个值，或者如果指定，则返回 `with` 子句中表达式的类型。例如：
```verilog
class C;
    rand bit [7:0] A[] ;
    constraint c1 { A.size == 5; }
    constraint c2 { A.sum() with (int'(item)) < 1000; }
endclass
```

约束 c2 将被解释为
```verilog
( int'(A[0])+int'(A[1])+int'(A[2])+int'(A[3])+int'(A[4]) ) < 1000
```

### 18.5.9 全局约束
当一个类的对象成员声明为 rand 时，所有的约束和随机变量都会与其他类变量和约束同时随机化。涉及其他对象的随机变量的约束表达式称为 *全局约束*（参见图 18-2）。
```verilog
class A; // 叶节点 
    rand bit [7:0] v;
endclass

class B extends A; // 堆节点
    rand A left;
    rand A right;
    constraint heapcond { left.v <= v; right.v > v; }
endclass
```
![gc](18-2.png)

图 18-2—全局约束

这个例子使用全局约束定义有序二叉树的合法值。类 A 表示一个具有 8 位值 v 的叶节点。类 B 扩展类 A，表示一个具有值 v、左子树和右子树的堆节点。两个子树都声明为 `rand`，以便在与其他类变量同时随机化时随机化它们。名为 heapcond 的约束块有两个全局约束，将左子树和右子树值与堆节点值相关联。当类 B 的实例被随机化时，求解器同时解决 B 及其左右子树，这些子树可以是叶节点或更多的堆节点。

以下规则确定哪些对象、变量和约束将被随机化：
 - `a)` 首先，确定要作为整体随机化的对象集。从调用 randomize() 方法的对象开始，添加所有包含在其中的对象，声明为 `rand`，并且是活动的（参见 18.8）。定义是递归的，并包括从起始对象到达的所有活动随机对象。在此步骤中选择的对象称为 *活动随机对象*。
 - `b)` 其次，从活动随机对象集合中选择所有活动约束。这些是应用于问题的约束。
 - `c)` 第三，从活动随机对象集合中选择所有活动随机变量。这些是要随机化的变量。所有其他变量引用被视为状态变量，其当前值被用作常量。

### 18.5.10 变量排序
求解器应确保随机值的选择使得合法值组合的值分布均匀（即，所有合法值组合具有相同的概率成为解）。这一重要属性保证了所有合法值组合的概率相等，从而使得随机化能够更好地探索整个设计空间。

有时，希望强制某些组合比其他组合更频繁地发生。考虑一个 1 位控制变量 s 限制 32 位数据值 d 的情况：
```verilog
class B;
    rand bit s;
    rand bit [31:0] d;
    constraint c { s -> d == 0; }
endclass
```

约束 c 表示 “s 蕴含 d 等于零”。尽管这看起来像 s 决定 d，实际上 s 和 d 是一起确定的。{s,d} 的合法值组合有 1 + 2^32 个，但是 s 只有一个为真。表 18-1 列出了每个合法值组合及其发生的概率：

表 18-1—无序约束 c 的合法值概率
| s | d | 概率 |
|---|---|------|
| 1 | `'h00000000` | 1/(1 + 2^32) |
| 0 | `'h00000000` | 1/(1 + 2^32) |
| 0 | `'h00000001` | 1/(1 + 2^32) |
| 0 | `'h00000002` | 1/(1 + 2^32) |
| 0 | ... | |
| 0 | `'hfffffffe` | 1/(1 + 2^32) |
| 0 | `'hffffffff` | 1/(1 + 2^32) |

约束提供了机制用于排序变量，所以 s 可以独立于 d 被选择。这种机制定义了变量评估的部分顺序，并使用 `solve` 关键字指定。

```verilog
class B;
    rand bit s;
    rand bit [31:0] d;
    constraint c { s -> d == 0; }
    constraint order { solve s before d; }
endclass
```

在这种情况下，order 约束告诉求解器在解决 d 之前解决 s。效果是 s 现在以 `50/50%` 的概率选择 0 或 1，然后 d 选择受 s 值约束。添加这个 order 约束不会改变合法值组合的集合，但会改变它们的发生概率，如表 18-2 所示：

表 18-2—有序约束 c 的合法值概率
| s | d | 概率 |
|---|---|------|
| 1 | `'h00000000` | 1/2 |
| 0 | `'h00000000` | 1/2 × 1/(1 + 2^32) |
| 0 | `'h00000001` | 1/2 × 1/(1 + 2^32) |
| 0 | `'h00000002` | 1/2 × 1/(1 + 2^32) |
| 0 | ... | |
| 0 | `'hfffffffe` | 1/2 × 1/(1 + 2^32) |
| 0 | `'hffffffff` | 1/2 × 1/(1 + 2^32) |

注意，d == 0 的概率为 1/(1 + 2^32)，接近 0%，没有 order 约束，而且是 1/2 × 1/(1 + 2^32)，略高于 50%，有 order 约束。

变量排序可以用于强制选择某些边界情况比它们本来会更频繁地发生。然而，“`solve...before...`” 约束不会改变解空间，因此不能导致求解器失败。

在约束块中定义变量顺序的语法如下 18-8。
---
```verilog
constraint_block_item ::= // from A.1.10
solve solve_before_list before solve_before_list ;
| constraint_expression 
solve_before_list ::= solve_before_primary { , solve_before_primary } 
solve_before_primary ::= [ implicit_class_handle . | class_scope ] hierarchical_identifier select 
```
---
语法 18-8—Solve...before 约束排序语法（摘自附录 A）

以下限制适用于变量排序：
 - 只允许随机变量，即它们应该是 `rand`。
 - 不允许 `randc` 变量。`randc` 变量总是在任何其他变量之前解决。
 - 变量应该是整数值。
 - 约束块可以包含常规值约束和排序约束。
 - 排序中不得存在循环依赖，例如“solve a before b”与“solve b before a”结合。
 - 没有明确排序的变量将与最后一组排序变量一起解决。这些值被推迟到尽可能晚，以确保值的分布良好。
 - 部分排序的变量将与最新的排序变量一起解决，以满足所有排序约束。这些值被推迟到尽可能晚，以确保值的分布良好。
 - 变量可以按照与排序约束不一致的顺序解决，只要结果相同。可能发生这种情况的一个示例情况如下：
   ```verilog
   x == 0;
   x < y;
   solve y before x;
   ```
   
   在这种情况下，因为 x 只有一个可能的赋值（0），所以 x 可以在 y 之前解决。求解器可以使用这种灵活性来加快求解过程。

### 18.5.11 静态约束块
通过在其定义中包含 static 关键字，可以将约束块定义为静态的。

声明静态约束块的语法如下 18-9。
---
```verilog
constraint_declaration ::= // from A.1.10
[ static ] constraint constraint_identifier constraint_block 
```
---
语法 18-9—静态约束语法（摘自附录 A）

如果约束块声明为 `static`，则调用 constraint_mode() 将影响所有对象中指定约束的所有实例。因此，如果将静态约束设置为 OFF，则该特定类的所有实例都将关闭。

当使用约束原型和外部约束块声明约束时，应用 `static` 关键字应用于约束原型和外部约束块，或者两者都不应用 static 关键字。如果一个应用了 static 关键字而另一个没有，则应该是一个错误。同样，纯约束可以应用 `static` 关键字，但任何覆盖约束必须匹配纯约束的资格或缺失。如果一个应用了 static 关键字而另一个没有，则应该是一个错误。

### 18.5.12 约束中的函数
有时，一些属性难以或无法在单个表达式中表达。例如，计算打包数组中的 1 的数量的自然方法使用循环：
```verilog
function int count_ones ( bit [9:0] w );
    for( count_ones = 0; w != 0; w = w >> 1 )
        count_ones += w & 1'b1;
endfunction
```

这样的函数可以用于将其他随机变量约束为 1 位的数量：
```verilog
constraint C1 { length == count_ones( v ) ; } 
```

如果不能调用函数，则需要展开循环并将其表示为单个位的和：
```verilog
constraint C2 
{
    length == ((v>>9)&1) + ((v>>8)&1) + ((v>>7)&1) + ((v>>6)&1) + ((v>>5)&1) +
((v>>4)&1) + ((v>>3)&1) + ((v>>2)&1) + ((v>>1)&1) + ((v>>0)&1); 
}
```

与 count_ones 函数不同，需要临时状态或无界循环的更复杂属性可能无法转换为单个表达式。因此，调用函数的能力增强了约束语言的表达能力，并减少了错误的可能性。上面的两个约束 C1 和 C2 并不完全等价；C2 是双向的（length 可以约束 v，反之亦然），而 C1 不是。

为了处理这些常见情况，SystemVerilog 允许约束表达式包含函数调用，但它施加了一些语义限制，如下所示：
 - 出现在约束表达式中的函数不能包含 `output` 或 `ref` 参数（`const ref` 是允许的）。
 - 出现在约束表达式中的函数应该是自动的（或不保留状态信息）且没有副作用。
 - 出现在约束中的函数不能修改约束，例如调用 rand_mode 或 constraint_mode 方法。
 - 函数应在解决约束之前被调用，并且它们的返回值应被视为状态变量。
 - 作为函数参数的随机变量应建立隐式变量排序或优先级。仅包含具有更高优先级的变量的约束在其他较低优先级约束之前解决。作为更高优先级约束的一部分解决的随机变量成为剩余约束的状态变量。例如：
   ```verilog
   class B;
       rand int x, y;
       constraint C { x <= F(y); } 
       constraint D { y inside { 2, 4, 8 } ; } 
   endclass
   ```

   强制 y 在 x 之前解决。因此，约束 D 在约束 C 之前单独解决，约束 C 使用 y 和 F(y) 的值作为状态变量。在 SystemVerilog 中，由函数参数变量排序暗示的行为与使用“`solve...before...`”约束指定的行为不同；函数参数变量排序将解决空间细分，从而改变它。因为仅解决具有更高优先级的变量的约束，而不考虑其他较低优先级约束，这种细分可能导致整体约束失败。在每个优先级约束集内，循环（`randc`）变量首先解决。
 - 由隐式变量排序创建的循环依赖将导致错误。
 - 在活动约束中执行函数调用的次数（至少一次）和顺序不确定。

### 18.5.13 约束保护
约束保护是谓词表达式，用作约束创建的保护，而不是求解器满足的逻辑关系。这些谓词表达式在解决约束之前评估，并且只包含以下项：
 - 常量
 - 状态变量
 - 对象句柄比较（两个句柄之间的比较或句柄与常量 `null` 之间的比较）

除了这些之外，迭代约束（参见 18.5.8）还考虑循环变量和正在迭代的数组的大小作为状态变量。

将这些谓词表达式视为约束保护可以防止求解器生成评估错误，从而在某些看似正确的约束上失败。这使用户能够编写约束，避免由于不存在的对象句柄或数组索引超出范围而导致的错误。例如，下面是单链表 SList 的排序约束，旨在分配一个按升序排序的随机数序列。然而，当 `next.n` 导致由于不存在的句柄而导致评估错误时，约束表达式将在最后一个元素上失败。
```verilog
class SList;
    rand int n;
    rand Slist next;
    constraint sort { n < next.n; }
endclass
```

通过编写谓词表达式来防止这种错误条件：
```verilog
constraint sort { if( next != null ) n < next.n; }
```

在上面的排序约束中，`if` 防止在 `next == null` 时创建约束，从而避免访问不存在的对象。蕴含（`->`）和 `if...else` 都可以用作保护。

保护表达式本身可能包含导致评估错误的子表达式（例如，空引用），并且也受到保护以防止生成错误。这种逻辑筛选通过使用以下 4 状态表示来评估谓词子表达式：
 - 0 FALSE：子表达式评估为 FALSE。
 - 1 TRUE：子表达式评估为 TRUE。
 - E ERROR：子表达式导致评估错误。
 - R RANDOM：表达式包含随机变量，无法评估。

谓词表达式中的每个子表达式都会评估为上述四个值之一。子表达式按任意顺序评估，其结果加上逻辑操作定义了备用 4 状态表示中的结果。子表达式的合取（`&&`）、析取（`||`）或否定（`!`）可以包含一些（也许全部）保护子表达式。以下规则指定了保护的结果：
 - 合取（`&&`）：如果任何一个子表达式评估为 FALSE，则保护评估为 FALSE。如果任何一个子表达式评估为 ERROR，则保护评估为 ERROR。否则，保护评估为 TRUE。
   - 如果保护评估为 FALSE，则约束被消除。
   - 如果保护评估为 TRUE，则生成（可能是条件的）约束。
   - 如果保护评估为 ERROR，则生成错误并且随机化失败。
 - 析取（`||`）：如果任何一个子表达式评估为 TRUE，则保护评估为 TRUE。如果任何一个子表达式评估为 ERROR，则保护评估为 ERROR。否则，保护评估为 FALSE。
   - 如果保护评估为 FALSE，则生成（可能是条件的）约束。
   - 如果保护评估为 TRUE，则生成无条件约束。
   - 如果保护评估为 ERROR，则生成错误并且随机化失败。
 - 否定（`!`）：如果子表达式评估为 ERROR，则保护评估为 ERROR。否则，如果子表达式评估为 TRUE 或 FALSE，则保护评估为 FALSE 或 TRUE，分别。

这些规则由图 18-3 中所示的真值表所规定。

![ttfcdanr](18-3.png)

图 18-3—合取、析取和否定规则的真值表

这些规则递归地应用，直到所有子表达式被评估。最终评估的谓词表达式的结果如下：
 - 如果结果为 TRUE，则生成无条件约束。
 - 如果结果为 FALSE，则约束被消除，不会生成错误。
 - 如果结果为 ERROR，则生成无条件错误并且随机化失败。
 - 如果评估的最终结果为 RANDOM，则生成条件约束。

当最终值为 RANDOM 时，需要遍历谓词表达式树以收集所有评估为 RANDOM 的条件保护。当最终值为 ERROR 时，不需要对表达式树进行后续遍历，从而允许实现只发出一个错误。

例1：
```verilog
class D;
    int x;
endclass

class C;
    rand int x, y;
    D a, b;
    constraint c1 { (x < y || a.x > b.x || a.x == 5) -> x + y == 10; }
endclass
```

在例 1 中，谓词子表达式是 `(x < y)`、`(a.x > b.x)` 和 `(a.x == 5)`，它们都由析取连接。一些可能的情况如下：
 - 情况 1：a 是非空，b 是空，a.x 是 5。
   - 因为 `(a.x==5)` 为真，b.x 生成错误不会导致错误。
   - 生成无条件约束 `(x+y == 10)`。
 - 情况 2：a 是空。
   - 这总是导致错误，无论其他条件如何。
 - 情况 3：a 是非空，b 是非空，a.x 是 10，b.x 是 20。
   - 所有保护子表达式评估为 FALSE。
   - 生成条件约束 `(x<y) -> (x+y == 10)`。

例 2：
```verilog
class D;
    int x;
endclass

class C;
    rand int x, y;
    D a, b;
    constraint c1 { (x < y && a.x > b.x && a.x == 5) -> x + y == 10; }
endclass
```

在例 2 中，谓词子表达式是 `(x < y)`、`(a.x > b.x)` 和 `(a.x == 5)`，它们都由合取连接。一些可能的情况如下：
 - 情况 1：a 是非空，b 是空，a.x 是 6。
   - 因为 `(a.x==5)` 为假，b.x 生成错误不会导致错误。
   - 约束被消除。
 - 情况 2：a 是空。
   - 这总是导致错误，无论其他条件如何。
 - 情况 3：a 是非空，b 是非空，a.x 是 5，b.x 是 2。
   - 所有保护子表达式评估为 TRUE。
   - 生成条件约束 `(x<y) -> (x+y == 10)`。

例 3：
```verilog
class D;
    int x;
endclass

class C;
    rand int x, y;
    D a, b;
    constraint c1 { (x < y && (a.x > b.x || a.x == 5)) -> x + y == 10; }
endclass
```

在例 3 中，谓词子表达式是 `(x < y)` 和 `(a.x > b.x || a.x == 5)`，它们由析取连接。一些可能的情况如下：
 - 情况 1：a 是非空，b 是空，a.x 是 5。
   - 保护表达式评估为 `(ERROR || a.x==5)`，评估为 `(ERROR || TRUE)`。
   - 保护子表达式评估为 TRUE。
   - 生成条件约束 `(x<y) -> (x+y == 10)`。
 - 情况 2：a 是非空，b 是空，a.x 是 8。
   - 保护表达式评估为 `(ERROR || FALSE)`，生成错误。
 - 情况 3：a 是空。
   - 这总是导致错误，无论其他条件如何。
 - 情况 4：a 是非空，b 是非空，a.x 是 5，b.x 是 2。
   - 所有保护子表达式评估为 TRUE。
   - 生成条件约束 `(x<y) -> (x+y == 10)`。
   - 

### 18.5.14 软约束
到目前为止描述的（正常）约束可以称为 *硬约束*，因为求解器必须始终满足它们，否则会导致求解器失败。相反，定义为 *软* 的约束的约束表达式指定了一个约束，除非被另一个约束（硬约束或优先级更高的软约束）所否定，否则必须满足。

软约束使得通用验证块的作者能够提供完整的工作环境，更容易扩展，因为求解器会自动忽略被后续更专业的约束所覆盖的通用软约束。软约束通常用于为随机变量指定默认值和分布。例如，通用数据包类的作者可能添加一个约束以确保默认情况下生成合法大小的数据包（在没有其他约束的情况下）：
```verilog
class Packet;
    rand int length;
    constraint deflt { soft length inside {32,1024}; }
endclass

Packet p = new();
p.randomize() with { length == 1512; }
```

如果通用约束 deflt 未定义为软约束，则调用 randomize 将失败并需要特殊处理。失败可能通过显式关闭约束来解决，这需要额外的过程代码，或者通过使用一个新类来扩展基类并用新的约束覆盖它，这显著复杂化了测试。相反，由软约束指定的默认值将被自动覆盖，这将导致一个更简单的分层测试。

#### 18.5.14.1 软约束优先级
软约束只表达对一个解决方案优于另一个解决方案的偏好；当它们被其他更重要的约束所否定时，它们将被丢弃。硬约束必须始终满足；它们永远不会被丢弃，因此被认为是最高优先级的。相反，软约束可能被硬约束或其他更高优先级的软约束所覆盖，因此，每个软约束都应与特定优先级相关联。软优先级设计为最后由用户指定的约束将优先。因此，验证环境中的后续层中指定的约束将比前面层中的约束具有更高的优先级。

以下规则确定软约束的优先级：
 - 在相同构造（约束块、类或结构）范围内的约束相对于其语法声明顺序分配优先级。在构造中后出现的约束具有更高的优先级。
 - 在外部约束块中的约束相对于类中约束原型（extern 声明）的声明顺序分配优先级。优先级取决于原型声明而不是 out-of-body 声明。在类中后出现的原型具有更高的优先级。
 - 包含对象（rand 类句柄）中的约束优先级低于容器对象（类或结构）中的所有约束。
 - 每个包含对象（rand 类句柄）中的约束相对于其类句柄的声明顺序分配优先级。在容器对象（类或结构）中后出现的类句柄具有更高的优先级。如果同一对象包含多次，则包含对象中的约束将具有最高优先级对象的优先级——最后声明的对象的优先级。
 - 派生类中的约束优先级高于其超类中的所有约束。
 - 内联约束块中的约束优先级高于被随机化的类中的约束。
 - 在 foreach 中的软约束的优先级由迭代顺序定义；后续迭代具有更高的优先级。如果关联数组的索引类型的关系运算符未定义，则优先级是实现相关的。

以下示例说明了上述规则：
```verilog
class B1;
    rand int x;
    constraint a { soft x > 10 ; soft x < 100 ; }
endclass              /* a1 */     /* a2 */

class D1 extends B1;
    constraint b { soft x inside {[5:9]} ; }
endclass              /* b1 */

class B2;
    rand int y;
    constraint c { soft y > 10 ; }
endclass              /* c1 */

class D2 extends B2;
    constraint d { soft y inside {[5:9]} ; }
    constraint e ;      /* d1 */
    rand D1 p1;
    rand B1 p2;
    rand D1 p3;
    constraint f { soft p1.x < p2.x ; }
endclass              /* f1 */

constraint D2::e { soft y > 100 ; } /* e1 */

D2 d = new();
initial begin
    d.randomize() with { soft y inside {10,20,30} ; soft y < p1.x ; };
end                           /* i1 */                /* i2 */
```

上面示例中软约束的相对优先级（从高到低）是：

i2→i1→f1→e1→d1→c1→p3.b1→p3.a2→p3.a1→p2.a2→p2.a1→p1.b1→p1.a2→p1.a1

如果句柄 p1 和 p3 引用相同的对象，则相对优先级是：

i2→i1→f1→e1→d1→c1→p3.b1→p3.a2→p3.a1→p2.a2→p2.a1

软约束只能为随机变量指定；不能为 randc 变量指定。

约束求解器实现了以下概念模型：
 - 考虑两个软约束 c1 和 c2，c1 的优先级高于 c2。
   1) 求解器首先尝试生成满足 c1 和 c2 的解决方案。
   2) 如果在（1）中失败，则尝试生成仅满足 c1 的解决方案。
   3) 如果在（2）中失败，则尝试生成仅满足 c2 的解决方案。
   4) 如果在（3）中失败，则丢弃 c1 和 c2。
 - 求解器应满足以下属性：
   - 如果调用 randomize 仅涉及软约束，则调用永远不会失败。
   - 如果软约束不显示任何矛盾，则结果与所有约束都声明为硬约束的结果相同。

#### 18.5.14.2 丢弃软约束
对随机变量的 `disable soft` 约束指定，所有引用给定随机变量的较低优先级软约束都应被丢弃。例如：
```verilog
class A;
    rand int x;
    constraint A1 { soft x == 3; }
    constraint A2 { disable soft x; } // 丢弃软约束
    constraint A3 { soft x inside { 1, 2 }; }
endclass

initial begin
    A a = new();
    a.randomize();
end
```

约束 A2 指示求解器丢弃对随机变量 x 的较低优先级软约束，导致约束 A1 被丢弃。因此，求解器只需满足最后一个约束 A3。因此，上面的示例将导致随机变量 x 取值 1 和 2。请注意，如果省略约束 A3，则变量将不受约束。

`disable soft` 约束导致较低优先级软约束被丢弃，无论这些约束是否创建矛盾。这个特性非常有用，可以将解决方案空间扩展到任何先前软约束指定的默认值之外。以下示例说明了这种行为：
```verilog
class B;
    rand int x;
    constraint B1 { soft x == 5; }
    constraint B2 { disable soft x; soft x dist {5, 8};}
endclass

initial begin
    B b = new();
    b.randomize();
end
```

在这个示例中，B2 中的 `disable soft` 约束导致 B1 中的较低优先级变量 x 的约束被丢弃。因此，求解器将为 x 分配值 5 和 8，分布相等——解决约束：x dist {5,8}。

与上面的示例相比，当省略 `disable soft` 约束时的行为如下：
```verilog
class B;
    rand int x;
    constraint B1 { soft x == 5; }
    constraint B3 { soft x dist {5, 8}; }
endclass

initial begin
    B b = new();
    b.randomize();
end
```

在上面的示例中，B3 中的软分布约束可以满足值 5。因此，求解器将为 x 分配值 5。通常，如果希望满足软分布约束的分布权重，则应首先丢弃那些较低优先级的软约束。

## 18.6 随机化方法
## 18.6.1 随机化()
对象中的变量使用 randomize() 类方法随机化。每个类都有一个内置的 randomize() 虚方法，声明如下：
```verilog
virtual function int randomize();
```

randomize() 方法是一个虚方法，它为对象中的所有活动随机变量生成随机值，这些随机变量受活动约束的约束。

randomize() 方法在成功设置所有随机变量和对象的有效值时返回 1；否则，返回 0。

例：
```verilog
class SimpleSum;
    rand bit [7:0] x, y, z;
    constraint c { z == x + y; }
endclass
```

这个类定义声明了三个随机变量 x、y 和 z。调用 SimpleSum 类的 randomize() 方法将随机化 SimpleSum 类的一个实例：
```verilog
SimpleSum p = new;
int success = p.randomize();
if (success == 1) ...
```

检查返回状态可能是必要的，因为状态变量的实际值或在派生类中添加约束可能使看似简单的约束不可满足。

## 18.6.2 pre_randomize() 和 post_randomize()
每个类都包含 pre_randomize() 和 post_randomize() 方法，这些方法在计算新的随机值之前和之后由 randomize() 方法自动调用。

pre_randomize() 方法的原型如下：
```verilog
function void pre_randomize();
```

post_randomize() 方法的原型如下：
```verilog
function void post_randomize();
```

当调用 obj.randomize() 时，它首先在 obj 上调用 pre_randomize()，并且还在所有启用的随机对象成员上调用 pre_randomize()。计算新的随机值并分配后，randomize() 在 obj 上调用 post_randomize()，并且还在所有启用的随机对象成员上调用 post_randomize()。

用户可以在任何类中重写 pre_randomize() 以在对象随机化之前执行初始化并设置前提条件。如果类是派生类且没有用户定义的 pre_randomize() 实现，则 pre_randomize() 将自动调用 super.pre_randomize()。

用户可以在任何类中重写 post_randomize() 以在对象随机化后执行清理、打印诊断和检查后置条件。如果类是派生类且没有用户定义的 post_randomize() 实现，则 post_randomize() 将自动调用 super.post_randomize()。

如果重写了这些方法，则它们应该调用其相关基类方法；否则，将跳过它们的预和后随机化处理步骤。

pre_randomize() 和 post_randomize() 方法不是虚方法。然而，因为它们由 randomize() 方法自动调用，而 randomize() 方法是虚方法，所以它们似乎表现得像虚方法一样。

### 18.6.3 随机化方法的行为
 - 在类中声明为静态的随机变量由该类的所有实例共享。每次调用 randomize() 方法时，该变量都会在每个类实例中更改。
 - 如果 randomize() 失败，则约束不可行，随机变量保留其先前值。
 - 如果 randomize() 失败，则不会调用 post_randomize()。
 - randomize() 方法是内置的，不能被覆盖。
 - randomize() 方法实现对象随机稳定性。可以通过调用其 srandom() 方法（参见 18.13.3）对对象进行种子化。
 - 内置方法 pre_randomize() 和 post_randomize() 是函数，不能阻塞。

## 18.7 内联约束——randomize() with
通过使用 randomize() `with` 构造，用户可以在调用 randomize() 方法的地方声明内联约束。这些额外的约束与类中声明的对象约束一起应用。

randomize() with 的语法如下 18-10：
---
```verilog
inline_constraint _declaration ::= // not in Annex A
class_variable_identifier . randomize [ ( [ variable_identifier_list | null ] ) ] 
with [ ( [ identifier_list ] ) ] constraint_block 
randomize_call ::= // from A.1.10
randomize { attribute_instance } 
[ ( [ variable_identifier_list | null ] ) ] 
[ with [ ( [ identifier_list ] ) ] constraint_block ]38
// 38) 在不是类类型对象的方法调用的 randomize_call 中，关键字 with 后的可选括号中的 identifier_list 是非法的，使用 null 也是非法。
```
---
语法 18-10—内联约束语法（摘自附录 A）

class_variable_identifier 是一个实例化对象的名称。

未命名的 constraint_block 包含要应用的额外内联约束，以及在类中声明的对象约束。

例如：
```verilog
class SimpleSum;
    rand bit [7:0] x, y, z;
    constraint c { z == x + y; }
endclass

task InlineConstraintDemo(SimpleSum p);
    int success;
    success = p.randomize() with { x < y; };
endtask
```

这是之前使用的相同示例；然而，使用 randomize() `with` 来引入一个额外的约束 x < y。

randomize() `with` 构造可以用在任何表达式可以出现的地方。`with` 后面的约束块可以定义与在类中声明的约束相同的约束类型和形式。

randomize() `with` 约束块也可以引用局部变量和子例程参数，消除了在对象类中将局部状态作为成员变量的需要。当约束块不是由可选的括号 identifier_list 引导时，约束块被认为是无限制的。在无限制的约束块中引用的变量名的解析范围从 randomize() `with` 对象类开始；也就是说，用于调用 randomize() `with` 方法的对象句柄的类。然后，如果一个名字在 randomize() `with` 对象类中无法解析，那么这个名字将按照通常的规则在包含内联约束的范围中解析。由 `this` 或 `super` 限定的名字将绑定到用于调用 randomize() `with` 方法的对象句柄的类。因此，如果限定名在 randomize() `with` 对象类中无法解析，那么限定名将被认为是错误的。除了由 this 或 super 限定的名字之外，点名将首先在向下的方式（参见 23.3）中解析，从 randomize() `with` 对象类的范围开始。如果点名在 randomize() `with` 对象类的范围中无法解析，那么它将按照通常的规则在包含内联约束的范围中解析。

`local::` 限定符（参见 18.7.1）用于绕过（randomize() `with` 对象）类的范围，并在包含 randomize 方法调用的（local）范围中开始名称解析。

当 constraint_block 由可选的括号 identifier_list 引导时，约束块被认为是 *受限制的*。在受限制的约束块中，只有以 identifier_list 开始的标识符的名称解析为 randomize() `with` 对象类；所有其他名称将从包含 randomize 方法调用的范围开始解析。当存在括号 identifier_list 时，使用 local:: 限定符，限定名将从包含 randomize 方法调用的范围开始解析，而不管该名称是否在 identifier_list 中。

在下面的示例中，randomize() `with` 类是 C1。
```verilog
class C1;
    rand integer x;
endclass

class C2;
    integer x;
    integer y;
    task doit(C1 f, integer x, integer z);
        int result;
        result = f.randomize() with { x < y + z; };
    endtask
endclass
```

在 f.randomize() `with` 约束块中，x 是 C1 类的成员，隐藏了 C2 中的 x。它也隐藏了 doit() 任务中的 x 参数。y 是 C2 的成员。z 是一个局部参数。

受限制的约束块可用于保证局部变量引用将解析为局部范围。
```verilog
class C;
    rand integer x;
endclass

function int F(C obj, integer y);
    F = obj.randomize() with (x) { x < y; };
endfunction
```

在这个示例中，只有 x 在对象 obj 中解析，因为只有 x 在 identifier_list 中列出。对 y 的引用永远不会绑定到 obj，即使后来添加了一个名为 y 的属性到类 C 中也是如此。

### 18.7.1 local:: 作用域解析
randomize() `with` 约束块可以引用类属性和方法调用的局部变量。无限制的内联约束块中的未限定名称首先在 randomize() `with` 对象类的范围内解析，然后在包含 randomize 方法调用的范围（局部范围）内解析。`local::` 限定符修改解析搜索顺序。当应用于内联约束中的标识符时，`local::` 限定符绕过 randomize() `with` 对象类的范围，并在局部范围中解析标识符。

在下面的示例中，randomize() `with` 类是 C，局部范围是函数 F()：
```verilog
class C;
    rand integer x;
endclass

function int F(C obj, integer x);
    F = obj.randomize() with { x < local::x; };
endfunction
```

在 obj.randomize() 调用的无限制内联约束块中，未限定名称 x 绑定到类 C 的属性（正在随机化的对象的范围），而限定名称 local::x 绑定到函数 F() 的参数（局部范围）。

因此，以下规则适用：
 - 仅由 `this` 或 `super` 限定的名称将绑定到用于调用 randomize() `with` 方法的对象句柄的类。
 - 由 `local::` 限定的名称将绑定到包含 randomize 方法调用的局部范围，包含特殊名称 `this` 或 `super`（即，`local::this`）。
 - `local::` 前缀可用于限定类范围和类型名称。
 - 就通配符包导入而言，语法形式 `local::a` 与在局部范围中声明的未限定名称 a 语义上相同。
 - 给定一个方法调用 obj.randomize() `with`，名称 local::obj 将绑定到 randomize() `with` 对象类的范围。

## 18.8 禁用随机变量——rand_mode()
rand_mode() 方法可用于控制随机变量的活动或非活动。当随机变量处于非活动状态时，它被视为未声明为 `rand` 或 `randc`。非活动变量不会被 randomize() 方法随机化，它们的值被求解器视为状态变量。所有随机变量最初都是活动的。

rand_mode() 方法的语法如下：
```verilog
task object[.random_variable]::rand_mode( bit on_off );
```

或
```verilog
function int object.random_variable::rand_mode();
```

object 是任何表达式，产生随机变量所在的对象句柄。

random_variable 是要应用操作的随机变量的名称。如果未指定（仅在作为任务调用时允许），则操作应用于指定对象中的所有随机变量。

当作为任务调用时，rand_mode 方法的参数确定要执行的操作，如表 18-3 所示。

表 18-3—rand_mode 参数
| 值 | 含义 | 描述 |
| -- | -- | -- |
| 0 | OFF | 将指定的变量设置为非活动状态，因此在随后调用 randomize() 方法时不会被随机化。 |
| 1 | ON | 将指定的变量设置为活动状态，因此在随后调用 randomize() 方法时会被随机化。 |

对于未打包的数组变量，random_variable 可以使用相应的索引指定单个元素。省略索引会导致数组的所有元素受到调用的影响。

对于未打包的结构变量，random_variable 可以使用相应的成员指定单个成员。省略成员会导致结构的所有成员受到调用的影响。

如果随机变量是对象句柄，则只更改变量的模式，而不更改该对象中的随机变量的模式（请参见 18.5.9 中的全局约束）。

一个编译错误将被发出，如果指定的变量在类层次结构中不存在，或者它存在但未声明为 `rand` 或 `randc`。

当作为函数调用时，rand_mode() 返回指定随机变量的当前活动状态。如果变量是活动的（ON），则返回 1；如果变量是非活动的（OFF），则返回 0。

rand_mode() 函数形式仅接受单个变量；因此，如果指定的变量是未打包的数组，则应通过其索引选择单个元素。

例：
```verilog
class Packet;
    rand integer source_value, dest_value;
    ... other declarations
endclass

int ret;
Packet packet_a = new;
// 关闭对象中的所有变量
packet_a.rand_mode(0);

// ... 其他代码
// 启用 source_value
packet_a.source_value.rand_mode(1);

ret = packet_a.dest_value.rand_mode();
```

这个例子首先禁用对象 packet_a 中的所有随机变量，然后仅启用 source_value 变量。最后，它将 ret 变量设置为变量 dest_value 的活动状态。

rand_mode() 方法是内置的，不能被覆盖。

如果随机变量被声明为 `static`，则随机变量的 rand_mode 状态也应该是静态的。例如，如果 rand_mode() 设置为非活动状态，则随机变量在基类的所有实例中都是非活动的。

## 18.9 控制约束——constraint_mode()
constraint_mode() 方法可用于控制约束的活动或非活动。当约束处于非活动状态时，它不会被 randomize() 方法考虑。所有约束最初都是活动的。

constraint_mode() 方法的语法如下：
```verilog
task object[.constraint_identifier]::constraint_mode( bit on_off );
```

或
```verilog
function int object.constraint_identifier::constraint_mode();
```

object 是任何表达式，产生约束所在的对象句柄。

constraint_identifier 是要应用操作的约束块的名称。约束名称可以是类层次结构中的任何约束块的名称。如果未指定约束名称（仅在作为任务调用时允许），则操作应用于指定对象中的所有约束。

当作为任务调用时，constraint_mode 方法的参数确定要执行的操作，如表 18-4 所示。

表 18-4—constraint_mode 参数
| 值 | 含义 | 描述 |
| -- | -- | -- |
| 0 | OFF | 将指定的约束块设置为非活动状态，因此在随后调用 randomize() 方法时不会被考虑。 |
| 1 | ON | 将指定的约束块设置为活动状态，因此在随后调用 randomize() 方法时会被考虑。 |

如果约束块不存在于类层次结构中，或者存在但未声明为约束块，则将发出编译错误。

当作为函数调用时，constraint_mode() 返回指定约束块的当前活动状态。如果约束块是活动的（ON），则返回 1；如果约束块是非活动的（OFF），则返回 0。

例如：
```verilog
class Packet;
    rand integer source_value;
    constraint filter1 { source_value > 2 * m; }
endclass

function integer toggle_rand( Packet p );
    if ( p.filter1.constraint_mode() )
        p.filter1.constraint_mode(0);
    else
        p.filter1.constraint_mode(1);
    toggle_rand = p.randomize();
endfunction
```

在这个例子中，toggle_rand 函数首先检查指定 Packet 对象 p 中约束 filter1 的当前活动状态。如果约束是活动的，函数将其停用；如果它是非活动的，函数将其启用。最后，函数调用 randomize 方法为变量 source_value 生成一个新的随机值。

constraint_mode() 方法是内置的，不能被覆盖。

## 18.10 动态约束修改
有几种方法可以动态修改随机化约束，如下：
 - 蕴含和 `if-else` 风格约束允许声明谓词约束。
 - 使用 constraint_mode() 内置方法可以使约束块处于活动或非活动状态。最初，所有约束块都是活动的。非活动约束块在调用 randomize() 方法时被求解器忽略。
 - 使用 rand_mode() 内置方法可以使随机变量处于活动或非活动状态。最初，所有 `rand` 和 `randc` 变量都是活动的。非活动变量在调用 randomize() 方法时不会被随机化，它们的值被求解器视为状态变量。
 - 可以更改 `dist` 约束中的权重，影响选择集中特定值的概率。

## 18.11 内联随机变量控制
randomize() 方法可用于临时控制类实例或对象中的随机和状态变量集。当不带参数调用 randomize 方法时，它的行为如前面的子条款中所述，即为对象中的所有随机变量（声明为 rand 或 randc）分配新值，以便满足所有约束。当使用参数调用 randomize 时，这些参数指定该对象中的所有随机变量的完整集；所有其他变量在对象中被视为状态变量。例如，考虑以下类和调用 randomize 的示例：
```verilog
class CA;
    rand byte x, y;
    byte v, w;
    constraint c1 { x < v && y > w; }
endclass

CA a = new;

a.randomize(); // 随机变量：x, y 状态变量：v, w
a.randomize( x ); // 随机变量：x 状态变量：y, v, w
a.randomize( v, w ); // 随机变量：v, w 状态变量：x, y
a.randomize( w, x ); // 随机变量：w, x 状态变量：y, v
```

这种机制控制了 randomize() 方法的活动随机变量集，这在概念上等同于对 rand_mode() 方法进行一组调用，以禁用或启用相应的随机变量。使用参数调用 randomize() 允许更改任何类属性的随机模式，即使这些属性未声明为 `rand` 或 `randc`。这种机制不会影响周期性随机模式；它不能将非随机变量更改为周期性随机变量（`randc`）并且不能将周期性随机变量更改为非周期性随机变量（从 `randc` 更改为 `rand`）。

randomize 方法的参数范围是对象类。参数限于调用对象的属性名称；不允许表达式。只有在调用 randomize 的范围内才能更改局部类成员的随机模式，也就是在声明局部成员的类的范围内。

### 18.11.1 内联约束检查器
通常，调用没有随机变量的类的 randomize 方法会导致该方法表现为检查器。换句话说，它不分配随机值，只返回状态：如果所有约束都满足，则返回 1，否则返回 0。内联随机变量控制机制也可以用于强制 randomize() 方法表现为检查器。

randomize 方法接受特殊参数 `null`，表示在调用期间没有随机变量。换句话说，所有类成员都被视为状态变量。这使得 randomize 方法表现为检查器而不是生成器。检查器评估所有约束，并且如果所有约束都满足，则只返回 1，否则返回 0。例如，如果之前定义的类 CA 执行以下调用：
```verilog
success = a.randomize( null ); // 没有随机变量
```

然后求解器将所有变量视为状态变量，并且只检查约束是否满足，即，使用 x、y、v 和 w 的当前值检查关系 (x < v && y > w) 是否为真。

## 18.12 随机化范围变量——std::randomize()
内置类 randomize 方法仅对类成员变量操作。使用类来建模要随机化的数据是一种强大的机制，它允许创建包含随机变量和约束的通用、可重用的对象，这些对象可以稍后扩展、继承、约束、覆盖、启用、禁用，并与其他对象合并或分离。类和相关随机变量和约束的易于操作性使类成为描述和操作随机数据和约束的理想工具。然而，一些不需要类的完整灵活性的问题可以使用更简单的机制来随机化不属于类的数据。作用域 randomize 函数 std::randomize() 允许用户在不需要定义类或实例化类对象的情况下在当前作用域中随机化数据。

作用域 randomize 函数的语法如下 18-11：
---
```verilog
scope_randomize ::= 
[ std:: ] randomize ( [ variable_identifier_list ] ) [ with constraint_block ] 
```
---
语法 18-11—作用域 randomize 函数语法（不在附录 A 中）

作用域 randomize 函数的行为与类 randomize 方法完全相同，只是它操作当前作用域中的变量而不是类成员变量。作为参数传递给此函数的变量指定要分配随机值的变量，即随机变量。

例如：
```verilog
module stim;
    bit [15:0] addr;
    bit [31:0] data;
    function bit gen_stim();
        bit success, rd_wr;
        success = randomize( addr, data, rd_wr ); // 调用 std::randomize
        return rd_wr;
    endfunction
    ...
endmodule
```

函数 gen_stim 使用三个变量 addr、data 和 rd_wr 作为参数调用 std::randomize()。因此，std::randomize() 为 gen_stim 函数作用域中可见的变量分配新的随机变量。在上面的示例中，addr 和 data 具有模块作用域，而 rd_wr 具有函数作用域。上面的示例也可以使用类编写：
```verilog
class stimc;
    rand bit [15:0] addr;
    rand bit [31:0] data;
    rand bit rd_wr;
endclass

function bit gen_stim( stimc p );
    bit [15:0] addr;
    bit [31:0] data;
    bit success;
    success = p.randomize();
    addr = p.addr;
    data = p.data;
    return p.rd_wr;
endfunction
```

然而，对于这种简单的应用，作用域 randomize 函数导致了一个直接的实现。

作用域 randomize 函数在成功设置所有随机变量为有效值时返回 1；否则，返回 0。如果调用作用域 randomize 函数时没有参数，则不会更改任何变量的值，而是检查其约束。将评估其约束块中的所有约束表达式，如果其中一个或多个表达式计算为 false（0），则 randomize 调用将返回 0；否则，返回 1。

### 18.12.1 向作用域变量添加约束——std::randomize() with
作用域 randomize 函数的 std::randomize() with 形式允许用户为局部作用域变量指定随机约束。当指定约束时，作用域 randomize 函数的参数变为随机变量；所有其他变量被视为状态变量。
```verilog
task stimulus( int length );
    int a, b, c, success;
    success = std::randomize( a, b, c ) with { a < b ; a + b < length ; }; 
    ...
    success = std::randomize( a, b ) with { b - a > length ; }; 
    ...
endtask
```

上面的任务 stimulus 在其局部变量 a、b 和 c 上调用 std::randomize 两次，为其局部变量 a、b 和 c 生成两组随机值。在第一次调用中，变量 a 和 b 被约束，使得变量 a 小于 b，它们的和小于任务参数 length，该参数被指定为状态变量。在第二次调用中，变量 a 和 b 被约束，使得它们的差大于状态变量 length。

## 18.13 随机数系统函数和方法
### 18.13.1 $urandom
系统函数 $urandom 提供了生成伪随机数的机制。该函数每次调用时返回一个新的 32 位随机数。该数应为无符号数。

$urandom 的语法如下：
```verilog
function int unsigned $urandom [ (int seed ) ] ;
```

seed 是一个可选参数，用于确定生成的随机数序列。种子可以是任何整数表达式。随机数生成器（RNG）将生成相同的随机数序列，每次使用相同的种子。

RNG 是确定性的。每次程序执行时，它都会循环通过相同的随机序列。通过使用外部随机变量（例如时间）对 $urandom 函数进行种子化，可以使该序列变得非确定性。

例如：
```verilog
bit [64:1] addr;
bit [ 3:0] number;

addr[32:1] = $urandom( 254 ); // 初始化生成器，获取 32 位随机数

addr = {$urandom, $urandom }; // 64 位随机数
number = $urandom & 15; // 4 位随机数
```

### 18.13.2 $urandom_range()
$urandom_range() 函数返回指定范围内的无符号整数。

$urandom_range() 的语法如下：
```verilog
function int unsigned $urandom_range( int unsigned maxval, int unsigned minval = 0 );
```

该函数将返回 maxval ... minval 范围内的无符号整数。

例 1：
```verilog
val = $urandom_range(7,0);
```

如果省略 minval，则函数将返回 maxval ... 0 范围内的值。

例 2：
```verilog
val = $urandom_range(7);
```

如果 maxval 小于 minval，则自动反转参数，使第一个参数大于第二个参数。

例 3：
```verilog
val = $urandom_range(0,7);
```

所有三个前面的例子都产生 0 到 7（包括）范围内的值。

$urandom_range() 自动线程稳定（参见 18.14.2）。

### 18.13.3 srandom()
srandom() 方法允许手动种子对象或线程的 RNG。可以使用进程的 srandom() 方法（参见 9.7）来种子进程的 RNG。

srandom() 方法的原型如下：
```verilog
function void srandom( int seed );
```

srandom() 方法使用给定种子的值初始化对象的 RNG。

### 18.13.4 get_randstate()
get_randstate() 方法检索对象的 RNG 的当前状态。使用进程的 get_randstate() 方法（参见 9.7）检索与进程关联的 RNG 的状态。

get_randstate() 方法的原型如下：
```verilog
function string get_randstate();
```

get_randstate() 方法返回与给定对象关联的 RNG 的内部状态的副本。

RNG 状态是一个长度和格式未指定的字符串。字符串的长度和内容是实现相关的。

### 18.13.5 set_randstate()
set_randstate() 方法设置对象的 RNG 的状态。使用进程的 set_randstate() 方法（参见 9.7）设置与进程关联的 RNG 的状态。

set_randstate() 方法的原型如下：
```verilog
function void set_randstate( string state );
```

set_randstate() 方法将给定状态复制到对象的 RNG 的内部状态中。

RNG 状态是一个长度和格式未指定的字符串。使用不是从 get_randstate() 或不同实现的 get_randstate() 获得的字符串值调用 set_randstate() 是未定义的。

## 18.14 随机稳定性
RNG 是本地化到线程和对象的。因为由线程或对象返回的随机值序列与其他线程或对象的 RNG 独立，所以这个属性被称为 *随机稳定性*。随机稳定性适用于以下情况：
 - 系统随机化调用，$urandom() 和 $urandom_range()
 - 对象和进程随机种子方法，srandom()
 - 对象随机化方法，randomize()

具有此特性的测试台在用户代码的小改动面前表现出更稳定的 RNG 行为。此外，它允许通过手动种子线程和对象来更精确地控制随机值的生成。

### 18.14.1 随机稳定性属性
随机稳定性包括以下属性：
 - *初始化 RNG*。每个模块实例、接口实例、程序实例和包都有一个初始化 RNG。每个初始化 RNG 都使用默认种子进行种子化。默认种子是一个实现相关的值。初始化 RNG 应用于创建静态进程和静态初始化程序（参见下面的列表项）。静态进程在附录 P 中定义。
 - *线程稳定性*。每个线程对该线程中调用的所有随机化系统调用都有一个独立的 RNG。当创建新的动态线程时，其 RNG 从其父线程中获取下一个随机值作为种子。此属性称为 *层次种子化*。当创建静态进程时，其 RNG 从包含线程声明的模块实例、接口实例、程序实例或包的初始化 RNG 中获取下一个值进行种子化。
   程序和线程稳定性可以在线程创建和随机数生成与以前相同的顺序时实现。当向现有测试添加新线程时，可以将其添加到代码块的末尾，以保持先前创建的工作的随机数稳定性。
 - *对象稳定性*。每个类实例（对象）对该类中的所有随机化方法都有一个独立的 RNG。当使用 new 创建对象时，其 RNG 从创建对象的线程中获取下一个随机值作为种子。当使用静态声明初始化类对象时，没有活动线程；因此，创建对象的 RNG 从包含声明的模块实例、接口实例、程序实例或包的初始化 RNG 中获取下一个随机值进行种子化。
   对象稳定性应在对象和线程创建和随机数生成与以前相同的顺序时保持。为了保持随机数稳定性，可以在创建现有对象之后创建新对象、线程和随机数。
 - *手动种子化*。所有非初始化 RNG 都可以手动种子化。结合层次种子化，此功能允许用户仅使用子系统（层次子树）的根线程上的单个种子完全定义子系统的操作。

### 18.14.2 线程稳定性
`$urandom` 系统调用返回的随机数值独立于线程执行顺序。例如：
```verilog
integer x, y, z;
fork // 在线程开始时设置种子
    begin process::self.srandom(100); x = $urandom; end
    // 在线程中设置种子
    begin y = $urandom; process::self.srandom(200); end
    // 从线程 RNG 中获取 2 个值
    begin z = $urandom + $urandom; end
join
```

上面的程序片段说明了以下几个属性：
 - *线程局部性*。返回的 x、y 和 z 值与线程执行顺序无关。这是一个重要的属性，因为它允许开发独立、可控和可预测的子系统。
 - *层次种子化*。当创建线程时，其随机状态使用父线程的下一个随机值作为种子进行初始化。三个 fork 线程都是从父线程种子化的。

每个线程使用唯一的值进行种子化，该值仅由其父线程确定。线程执行子树的根确定其子树的随机种子。这允许整个子树被移动并通过手动种子化其根线程来保持其行为。

### 18.14.3 对象稳定性
每个类内部构建的 randomize() 方法展现出对象稳定性。这是在每个实例内的 randomize() 调用独立于其他实例，并且独立于其他随机化函数调用的属性。

例如：
```verilog
class C1;
    rand integer x;
endclass

class C2;
    rand integer y;
endclass

initial begin
    C1 c1 = new();
    C2 c2 = new();
    integer z;
    void'(c1.randomize());
    // z = $random;
    void'(c2.randomize());
end
```

 - c1.x 和 c2.y 的返回值是相互独立的。
 - randomize() 调用是独立于 $random 系统调用的。如果取消注释上面的 z = $random 行，则分配给 c1.x 和 c2.y 的值不会改变。
 - 每个实例都有一个独特的随机值来源，可以独立地进行种子化。该随机种子是在创建实例时从父线程中获取的。
 - 对象可以在任何时候使用 srandom() 方法进行种子化。
   ```verilog
   class C3
       function new (integer seed);
           // 为此实例设置一个新种子
           this.srandom(seed);
       endfunction
   endclass
   ```

一旦对象被创建，就不能保证创建线程可以在另一个线程访问对象之前更改对象的随机状态。因此，最好在 new 方法内部进行对象的自我种子化，而不是在外部。

对象的种子可以从任何线程设置。但是，线程的种子只能从线程内部设置。

## 18.15 手动种子化随机
每个对象保留其自己的内部 RNG，用于它的 randomize() 方法单独使用。这允许对象互相独立地随机化，并且与其他系统随机化函数的调用独立。当对象被创建时，其 RNG 从创建对象的线程中获取下一个随机值作为种子。这种过程称为 *层次对象种子化*。

有时期望手动种子化对象的 RNG。这可以通过调用对象的 srandom() 方法来实现。这也可以在在类方法内或类定义外部实现：

一个在内部设置 RNG 种子的实例，作为类方法，如下所示：
```verilog
class Packet;
    rand bit[15:0] header;
    ...
    function new (int seed);
        this.srandom(seed);
        ...
    endfunction
endclass
```

一个在外部设置 RNG 种子的实例，如下所示：
```verilog
Packet p = new(200); // 使用种子 200 创建 p
p.srandom(300); // 使用种子 300 重新设置 p
```

在对象的 new() 函数中调用 srandom() 方法确保对象的 RNG 在任何类成员值被随机化之前使用新种子设置。

## 18.16 随机加权 case 语句——randcase
---
```verilog
statement_item ::= // from A.6.4
...
| randcase_statement 
randcase_statement ::= // from A.6.7
randcase randcase_item { randcase_item } endcase
randcase_item ::= expression : statement_or_null
```
---
语法 18-12—Randcase 语法（摘自附录 A）

关键字 `randcase` 引入一个 `case` 语句，它随机选择其分支之一。randcase_item 表达式是构成分支权重的非负整数值。一个条目的权重除以所有权重的总和给出采取该分支的概率。例如：
```verilog
randcase
  3 : x = 1;
  1 : x = 2;
  4 : x = 3;
endcase
```

所有权重的总和是 8；因此，采取第一个分支的概率是 0.375，采取第二个分支的概率是 0.125，采取第三个分支的概率是 0.5。

如果一个分支指定了零权重，那么该分支不会被采取。如果所有 randcase_items 指定了零权重，那么没有分支被采取，并且可以发出警告。

randcase 权重可以是任意表达式，而不仅仅是常量。例如：
```verilog
byte a, b;

randcase
  a + b : x = 1;
  a - b : x = 2;
  a ^ ~b : x = 3;
  12'b800 : x = 4;
endcase
```

每个权重表达式的精度是自决的。权重的总和使用标准加法语义（所有权重的最大精度）计算，其中每个加数是无符号的。每个权重表达式最多计算一次（实现可以缓存相同的表达式）以未指定的顺序。在前面的示例中，前三个权重表达式使用 8 位精度计算，第四个表达式使用 12 位精度计算。结果权重作为无符号值使用 12 位精度相加。然后使用无符号 12 位比较选择权重。

每次调用 `randcase` 从 0 到权重总和中检索一个随机数。然后按声明顺序选择权重：较小的随机数对应于第一个（顶部）权重语句。

randcase 语句表现出线程稳定性。随机数是从 $urandom_range() 获取的；因此，绘制的随机值与线程执行顺序无关。这可能导致多次调用 $urandom_range() 来处理大于 32 位的值。

## 18.17 随机序列生成——randsequence
解析器生成器（如 yacc）使用 BNF 或类似的表示法来描述要解析的语言的语法。语法用于生成一个程序，该程序能够检查一系列标记是否表示该语言的语法正确的话语。SystemVerilog 的序列生成器颠倒了这个过程。它使用语法随机创建一个正确的语法描述语言的话语（即一系列标记）。随机序列生成器对于随机生成结构化激励序列（如指令或网络流量模式）非常有用。

序列生成器使用一组规则和在 `randsequence` 块中的产生。`randsequence` 块的语法如下 18-13：
---
```verilog
statement_item ::= // from A.6.4
...
| randsequence_statement 
randsequence_statement ::= randsequence ( [ production_ identifier ] ) // from A.6.12
production { production } 
endsequence
production ::= [ data_type_or_void ] production_identifier [ ( tf_port_list ) ] : rs_rule { | rs_rule } ;
rs_rule ::= rs_production_list [ := weight_specification [ rs_code_block ] ] 
rs_production_list ::= 
rs_prod { rs_prod } 
| rand join [ ( expression ) ] production_item production_item { production_item } 
weight_specification ::= 
integral_number 
| ps_identifier 
| ( expression )
rs_code_block ::= { { data_declaration } { statement_or_null } }
rs_prod ::= 
production_item 
| rs_code_block 
| rs_if_else 
| rs_repeat 
| rs_case 
production_item ::= production_identifier [ ( list_of_arguments ) ]
rs_if_else ::= if ( expression ) production_item [ else production_item ] 
rs_repeat ::= repeat ( expression ) production_item 
rs_case ::= case ( case_expression ) rs_case_item { rs_case_item } endcase
rs_case_item ::= 
case_item_expression { , case_item_expression } : production_item ;
| default [ : ] production_item ;
case_expression ::= expression // from A.6.7
case_item_expression ::= expression 
```
---
语法 18-13—Randsequence 语法（摘自附录 A）

`randsequence` 语法由一个或多个产生组成。每个产生包含一个名称和一个产生项列表。产生项进一步分为终结符和非终结符。非终结符以终结符和其他非终结符定义。终结符在其关联的代码块之外不需要进一步定义。最终，每个非终结符都被分解为其终结符。产生列表包含一系列产生项，指示这些项必须按顺序流式传输。单个产生可以包含多个由 `|` 符号分隔的产生列表。用 `|` 分隔的产生列表意味着生成器将随机选择。

一个简单的例子说明了基本概念：
```verilog
randsequence( main )
    main : first second done ;
    first : add | dec ;
    second : pop | push ;
    done : { $display("done"); } ;
    add : { $display("add"); } ;
    dec : { $display("dec"); } ;
    pop : { $display("pop"); } ;
    push : { $display("push"); } ;
endsequence
```

产生 main 以三个非终结符 first、second 和 done 定义。当选择 main 时，它生成序列 first、second 和 done。当生成 first 产生时，它被分解为其产生，该产生指定在 add 和 dec 之间进行随机选择。类似地，第二个产生指定在 pop 和 push 之间进行选择。所有其他产生都是终结符；它们完全由其代码块指定，该代码块显示产生名称。因此，语法导致以下可能的结果：
 - add pop done
 - add push done
 - dec pop done
 - dec push done

当执行 `randsequence` 语句时，它生成一个由语法驱动的随机产生流。随着生成每个产生，执行其关联代码块的副作用产生所需的激励。除了基本语法外，序列生成器还提供随机权重、交错和其他控制机制。虽然 `randsequence` 语句本身不会创建循环，但递归产生将导致循环。

`randsequence` 语句创建一个自动作用域。所有产生标识符都是局部范围的。此外，`randsequence` 块中的每个代码块都创建一个匿名自动范围。不允许对在代码块中声明的变量进行层次引用。要声明静态变量，应使用 `static` 前缀。`randsequence` 关键字后面可以跟一个可选的产生名称（括号内），该名称指定顶级产生的名称。如果未指定，则第一个产生成为顶级产生。

### 18.17.1 随机产生权重
可以通过为产生列表分配权重来更改生成产生的概率。特定产生列表的概率与其指定的权重成正比。
---
```verilog
production ::= // from A.6.12
[ data_type_or_void ] production_identifier [ ( tf_port_list ) ] : rs_rule { | rs_rule } ;
rs_rule ::= rs_production_list [ := weight_specification [ rs_code_block ] ] 
```
---
语法 18-14—随机产生权重语法（摘自附录 A）

`:=` 运算符将 weight_specification 指定的权重分配给其产生列表。weight_specification 应计算为非负整数值。当分配给替代产生时，权重才有意义，即由 `|` 分隔的产生列表。权重表达式在选择其封闭产生时进行评估，从而允许权重动态更改。例如，前面示例的第一个产生可以重写为：
```verilog
first : add := 3
| dec := (1 + 1) // 2
;
```

这将使用两个加权产生列表 add 和 dec 定义产生 first。产生 add 将以 60% 的概率生成，产生 dec 将以 40% 的概率生成。

如果未指定权重，则产生将使用权重 1。如果只指定了一些权重，则未指定的权重将使用权重 1。

### 18.17.2 if-else 产生语句
通过 `if-else` 产生语句，可以有条件地生成产生。`if-else` 产生语句的语法如下 18-15：
---
```verilog
rs_if_else ::= if ( expression ) production_item [ else production_item ] // from A.6.12
```
---
语法 18-15—If-else 条件随机产生语法（摘自附录 A）

表达式可以是任何计算为布尔值的表达式。如果表达式计算为 true，则生成表达式后面的产生；否则生成可选 else 语句后面的产生。例如：
```verilog
randsequence()
    ...
    PP_PO : if ( depth < 2 ) PUSH else POP ;
    PUSH : { ++depth; do_push(); };
    POP : { --depth; do_pop(); };
endsequence
```

这个例子定义了产生 PP_OP。如果变量 depth 小于 2，则生成产生 PUSH。否则生成产生 POP。变量 depth 由 PUSH 和 POP 产生的代码块更新。

### 18.17.3 Case 产生语句
通过 `case` 产生语句，可以从一组备选项中选择产生。`case` 产生语句的语法如下 18-16：
---
```verilog
rs_case ::= case ( case_expression ) rs_case_item { rs_case_item } endcase // from A.6.12
rs_case_item ::= 
case_item_expression { , case_item_expression } : production_item ;
| default [ : ] production_item ;
case_expression ::= expression // from A.6.7
case_item_expression ::= expression 
```
---
语法 18-16—Case 产生语句语法（摘自附录 A）

`case` 产生语句类似于过程性 `case` 语句，除了以下几点。case_expression 被评估，并且它的值与每个 case_item_expression 的值进行比较。生成的产生是与 case_expression 匹配的第一个 case_item_expression 关联的产生。如果没有找到匹配的 case_item_expression，则生成与可选 default 项关联的产生，或者如果没有 default 项，则不生成任何内容。在一个 case 产生语句中多个 default 语句是非法的。通过逗号分隔的 case_item_expression 允许多个表达式共享产生。例如：
```verilog
randsequence()
    SELECT : case ( device & 7 )
    0 : NETWORK ; 
    1, 2 : DISK ; 
    default : MEMORY ;
    endcase ;
    ...
endsequence
```

这个例子定义了产生 SELECT，其中包含一个 case 语句。case_expression (device & 7) 被评估并与两个 case_item_expression 进行比较。如果表达式匹配 0，则生成产生 NETWORK；如果匹配 1 或 2，则生成产生 DISK。否则生成产生 MEMORY。

### 18.17.4 Repeat 产生语句
`repeat` 产生语句用于迭代产生指定次数的产生。`repeat` 产生语句的语法如下 18-17：
---
```verilog
rs_repeat ::= repeat ( expression ) production_item // from A.6.12
```
---
语法 18-17—Repeat 随机产生语法（摘自附录 A）

表达式应计算为非负整数值。该值指定生成产生的次数。例如：
```verilog
randsequence()
    ...
    PUSH_OPER : repeat( $urandom_range( 2, 6 ) ) PUSH ;
    PUSH : ...
endsequence
```

在这个例子中，PUSH_OPER 产生指定 PUSH 产生的随机次数（2 到 6 次），具体取决于 $urandom_range() 返回的值。

`repeat` 产生语句本身不能被提前终止。`break` 语句将终止整个 `randsequence` 块（参见 18.17.6）。

### 18.17.5 交错产生——rand join
`rand join` 产生控制用于在保持每个序列的相对顺序的同时随机交错两个或多个产生序列。`rand join` 产生控制的语法如下 18-18：
---
```verilog
rs_production_list ::= // from A.6.12
rs_prod { rs_prod }
| rand join [ ( expression ) ] production_item production_item { production_item }
```
---
语法 18-18—Rand join 随机产生语法（摘自附录 A）

例如：
```verilog
randsequence( TOP )
    TOP : rand join S1 S2 ;
    S1 : A B ;
    S2 : C D ;
endsequence
```

生成器将随机生成以下序列：
 - A B C D
 - A C B D
 - A C D B
 - C D A B
 - C A B D
 - C A D B

`rand join` 关键字后面可以跟一个实数，范围为 0.0 到 1.0。该表达式的值表示要交错的序列的长度如何影响选择序列的概率。序列的长度是在给定时间内尚未交错的产生数量。如果表达式为 0.0，则最短序列优先。如果表达式为 1.0，则最长序列优先。例如，使用前面的示例：
```verilog
TOP : rand join (0.0) S1 S2 ;
```

将优先选择序列：A B C D    C D A B，并且
```verilog
TOP : rand join (1.0) S1 S2 ;
```

将优先选择序列：A C B D    A C D B    C A B D    C A D B。

如果未指定，则生成器使用默认值 0.5，不优先任何序列长度。

在每一步，生成器将非终结符符号交错到深度 1。

### 18.17.6 中止产生——break 和 return
两个过程性语句可用于提前终止产生：`break` 和 `return`。这两个语句可以出现在任何代码块中；它们在退出的范围方面有所不同。

`break` 语句终止序列生成。当 `break` 语句在产生代码块中执行时，它强制跳出 randsequence 块。例如：
```verilog
randsequence()
    WRITE : SETUP DATA ;
    SETUP : { if( fifo_length >= max_length ) break; } COMMAND ;
    DATA : ...
endsequence
next_statement : ...
```

在前面的示例中，如果 SETUP 产生中执行 `break` 语句，则不会生成 COMMAND，并且执行将继续在标记为 next_statement 的行上。循环语句中使用 `break` 语句的行为如 12.8 中所定义。因此，`break` 语句终止最小的封闭循环语句；否则，它终止 randsequence 块。

`return` 语句中止当前产生。当 `return` 语句在产生代码块中执行时，当前产生被中止。序列生成将继续生成中止产生后的下一个产生。例如：
```verilog
randsequence()
    TOP : P1 P2 ;
    P1 : A B C ;
    P2 : A { if( flag == 1 ) return; } B C ;
    A : { $display( "A" ); } ;
    B : { if( flag == 2 ) return; $display( "B" ); } ;
    C : { $display( "C" ); } ;
endsequence
```

根据变量 flag 的值，上面的示例显示以下内容：
 - flag == 0 ==> A B C A B C
 - flag == 1 ==> A B C A
 - flag == 2 ==> A C A C

当 flag == 1 时，产生 P2 在中间被中止，生成 A。当 flag == 2 时，产生 B 被两次中止（一次作为 P1 的一部分，一次作为 P2 的一部分）；然而，每次生成都继续生成下一个产生 C。

### 18.17.7 产生之间的值传递
数据可以在要生成的产生之间传递，生成的产生可以将数据返回给触发其生成的非终结符。传递数据给产生类似于任务调用，并使用相同的语法。从产生返回数据需要为产生声明一个类型，该类型使用类似于函数声明的语法。

接受数据的产生包括一个形式参数列表。声明产生参数的语法类似于任务原型；将数据传递给产生的语法与任务调用相同（参见语法 18-19）。
---
```verilog
production ::= 
[ data_type_or_void ] production_identifier [ ( tf_port_list ) ] : rs_rule { | rs_rule } ; // from A.6.12
```
---
语法 18-19—随机产生语法（摘自附录 A）

例如，上面的第一个示例可以写成：
```verilog
randsequence( main )
    main : first second gen ;
    first : add | dec ;
    second : pop | push ;
    add : gen("add") ;
    dec : gen("dec") ;
    pop : gen("pop") ;
    push : gen("push") ;
    gen( string s = "done" ) : { $display( s ); } ;
endsequence
```

在这个例子中，产生 gen 接受一个字符串参数，其默认值为 "done"。另外五个产生生成这个产生，每个产生都有一个不同的参数（main 中的产生使用默认值）。

产生创建一个作用域，该作用域包含其所有规则和代码块。因此，传递给产生的参数在整个产生中都可用。

返回数据的产生需要声明一个类型。未指定返回类型的产生应假定为 void 返回类型。

通过使用带有表达式的 return 语句返回值。当 return 语句与返回值的产生一起使用时，应指定正确类型的表达式，就像非 void 函数一样。return 语句将给定的表达式分配给相应的产生。返回值可以在触发生成返回值的产生的非终结符的代码块中读取。在这些代码块中，返回值使用产生名称加上可选的索引表达式访问。

在规则中，为每个返回值产生隐式声明一个变量。变量的类型由产生的返回类型和产生在规则中出现的次数确定。如果产生只出现一次，则隐式变量的类型是产生的返回类型。如果产生出现多次，则类型是一个数组，其中元素类型是产生的返回类型。数组从 1 到产生在规则中出现的次数进行索引。数组的元素根据产生的实例返回的值按照出现的语法顺序进行分配。

例 1：
```verilog
randsequence( bin_op )
    void bin_op : value operator value // void 类型是可选的
    { $display("%s %b %b", operator, value[1], value[2]); }
    ;
    bit [7:0] value : { return $urandom; } ;
    string operator : add := 5 { return "+" ; }
    | dec := 2 { return "-" ; }
    | mult := 1 { return "*" ; }
    ;
endsequence
```

在上面的示例中，operator 和 value 产生返回一个字符串和一个 8 位值，分别。产生 bin_op 包括这两个返回值产生。因此，与产生关联的代码块具有以下隐式变量声明：
```verilog
bit [7:0] value [1:2];
string operator;
```

例 2：
```verilog
int cnt;
...
randsequence( A )
    void A : A1 A2;
    void A1 : { cnt = 1; } B repeat(5) C B 
    { $display("c=%d, b1=%d, b2=%d", C, B[1], B[2]); }
    ;
    void A2 : if (cond) D(5) else D(20) 
    { $display("d1=%d, d2=%d", D[1], D[2]); }
    ;
    int B : C { return C;}
    | C C { return C[2]; }
    | C C C { return C[3]; }
    ;
    int C : { cnt = cnt + 1; return cnt; };
    int D (int prm) : { return prm; };
endsequence
```

在例 2 中，产生 A1 的代码块具有以下隐式变量声明：
```verilog
int B[1:2];
int C;
```

产生 A2 的代码块具有以下隐式变量声明：
```verilog
int D[1:2];
```

如果 cond 为 true，则第一个元素被赋予由 D(5) 返回的值。如果 cond 为 false，则第二个元素被赋予由 D(20) 返回的值。

产生 B 的第一个规则的代码块具有以下隐式变量声明：
```verilog
int C;
```

产生 B 的第三个规则的代码块具有以下隐式变量声明：
```verilog
int C[1:3];
```

访问这些隐式变量会产生由相应产生返回的值。当执行上面的例子时，显示一个简单的三项随机序列：一个操作符，后面跟两个 8 位值。运算符 +、- 和 * 的选择概率分别为 5/8、2/8 和 1/8。

只能访问已生成的产生返回的值。尝试读取尚未生成的产生返回的值会导致未定义的值。例如：
```verilog
X : A {int y = B;} B ; // 无效使用 B
X : A {int y = A[2];} B A ; // 无效使用 A[2]
X : A {int y = A;} B {int j = A + B;} ; // 有效
```

由 randsequence 生成的序列可以直接驱动系统，作为产生生成的副作用，或者可以生成整个序列以供将来处理。例如，以下函数生成并返回一个队列，该队列包含在其参数中指定的范围内的随机数。队列的第一个和最后一个队列项分别对应于下限和上限。此外，队列的大小根据产生权重随机选择。
```verilog
function int[$] GenQueue(int low, int high);
    int[$] q;
    randsequence()
        TOP : BOUND(low) LIST BOUND(high) ;
        LIST : LIST ITEM := 8 { q = { q, ITEM }; }
        | ITEM := 2 { q = { q, ITEM }; }
        ;
        int ITEM : { return $urandom_range( low, high ); } ;
        BOUND(int b) : { q = { q, b }; } ;
    endsequence
    GenQueue = q;
endfunction
```

当在函数 GenQueue 中执行 randsequence 时，它生成 TOP 产生，导致生成三个产生：BOUND 与参数 low、LIST 和 BOUND 与参数 high。BOUND 产生简单地将其参数附加到队列。LIST 产生由加权 LIST ITEM 产生和 ITEM 产生组成。LIST ITEM 产生以 80% 的概率生成，这导致递归生成 LIST 产生，从而推迟 ITEM 产生的生成。每次生成 ITEM 产生时，它在指定范围内生成一个随机数，稍后附加到队列。

以下示例使用 randsequence 块生成 DSL 数据包网络的随机流量：
```verilog
class DSL; ... endclass // 创建有效 DSL

randsequence (STREAM)
    STREAM : GAP DATA := 80
    | DATA := 20 ;
    DATA : PACKET(0) := 94 { transmit( PACKET ); }
    | PACKET(1) := 6 { transmit( PACKET ); } ;
    DSL PACKET (bit bad) : { DSL d = new;
    if( bad ) d.crc ^= 23; // 损坏 crc
    return d;
    );
    GAP: { ## {$urandom_range( 1, 20 )}; };
endsequence
```

在这个例子中，流量由一系列（好和坏）数据包和间隔组成。第一个产生 STREAM 指定 80% 的时间流量由 GAP 后跟一些 DATA 组成，20% 的时间流量只由 DATA 组成（没有 GAP）。第二个产生 DATA 指定 94% 的所有数据包是好数据包，剩下的 6% 是坏数据包。PACKET 产生实现 DSL 数据包创建；如果产生参数为 1，则通过搅动有效的 DSL 数据包的 crc 来生成坏数据包。最后，GAP 产生实现传输间隔，等待 1 到 20 个周期之间的随机数量。
