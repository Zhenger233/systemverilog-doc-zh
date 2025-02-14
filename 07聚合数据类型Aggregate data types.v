# 7. 聚合数据类型
## 7.1 概述
本章描述以下内容：
 - 结构定义和使用
 - 联合定义和使用
 - 打包数组、未打包数组、动态数组、关联数组和队列
 - 数组查询和操作方法

## 7.2 结构
*结构* 表示可以整体引用的数据类型集合，或者可以按名称引用构成结构的各个数据类型。默认情况下，结构是未打包的，这意味着数据类型有实现相关的打包。未打包结构可以包含任何数据类型。

结构声明遵循 C 语法，但在“`{`”之前没有可选的结构标签。结构声明的语法如 7-1 所示。

---
```verilog
data_type ::= // from A.2.2.1
... 
| struct_union [ packed [ signing ] ] { struct_union_member { struct_union_member } }
{ packed_dimension }13 
struct_union_member16 ::= 
{ attribute_instance } [random_qualifier] data_type_or_void list_of_variable_decl_assignments ;
data_type_or_void ::= data_type | void
struct_union ::= struct | union [ tagged ] 
// 13) 当使用带有 struct 或 union 关键字的打包维度时，也应使用 packed 关键字。
// 16) 只有在标记联合内部才能声明 void struct_union_member。
```
---
语法 7-1——结构声明语法（摘自附录 A）

以下是声明结构的示例：
```verilog
struct { bit [7:0] opcode; bit [23:0] addr; } IR; // 匿名结构定义变量 IR

IR.opcode = 1; // 设置 IR 中的字段

typedef struct { 
    bit [7:0] opcode; 
    bit [23:0] addr; 
} instruction; // 命名结构类型
instruction IR; // 定义变量
```

### 7.2.1 打包结构
打包结构是将向量细分为子字段的机制，可以方便地作为成员访问。因此，打包结构由位字段组成，这些位字段在内存中紧密打包在一起，没有间隙。未打包结构具有依赖实现的打包，通常与 C 编译器匹配。打包结构与未打包结构的区别在于，当打包结构作为主要结构时，应将其视为单个向量。

打包结构可以整体使用算术和逻辑运算符。指定的第一个成员是最重要的，随后的成员按降低的重要性顺序排列。使用 `packed` 关键字声明结构，可以在后面跟随 `signed` 或 `unsigned` 关键字，根据所需的算术行为。默认为 unsigned。

```verilog
struct packed signed { 
    int a; 
    shortint b; 
    byte c; 
    bit [7:0] d;
} pack1; // 有符号，2 状态

struct packed insigned {
    time a;
    integer b;
    logic [31:0] c;
} pack2; // 无符号, 4 状态
```

未打包结构的符号是不允许的，下列声明将被认为非法：
```verilog
typedef struct signed {
int f1 ;
logic f2 ;
} sIllegalSignedUnpackedStructType; // 非法声明
```

如果打包结构内的所有数据类型都是 2 状态的，那么结构整体被视为 2 状态的。

如果打包结构内的任意数据类型是 4 状态的，那么结构整体被视为 4 状态的。如果结构中也包含2态成员，在读取这些成员时会发生从4态到2态的隐式转换，而在写入这些成员时则会发生从2态到4态的隐式转换。

打包结构体的一个或多个位可以像打包数组一样被选择，其范围为[n-1:0]：
```verilog
pack1 [15:8] // c
```

打包结构体中仅允许使用打包数据类型和表 6-8（见6.11）中总结的整数数据类型。

打包结构体可以与 `typedef` 一起使用。
```verilog
typedef struct packed { // 默认无符号
    bit [3:0] GFC; 
    bit [7:0] VPI; 
    bit [11:0] VCI; 
    bit CLP; 
    bit [3:0] PT ; 
    bit [7:0] HEC; 
    bit [47:0] [7:0] Payload; 
    bit [2:0] filler; 
} s_atmcell; 
```

### 7.2.2 给结构体赋值
结构体可以作为一个整体进行赋值，并且可以作为整体传递给子程序或从子程序返回。

结构体数据类型的成员可以通过在声明每个成员时使用初始赋值来分配单独的默认成员值。所赋值的表达式应当是常量表达式。

以下是初始化结构体类型成员的一个例子：
```verilog
typedef struct {
    int addr = 1 + constant;
    int crc;
    byte data [4] = '{4{1}};
} packet1;
```

然后可以实例化该结构体：
`packet1 p1; // 使用typedef中定义的初始化;p1.crc 将使用 int 的默认值`

如果在变量声明时使用了显式的初始值表达式，则结构体数据类型中的初始赋值表达式将被忽略。5.10 讨论了为结构体分配初始值。例如：
`packet1 pi = '{1,2,'{2,3,4,5}}; // 抑制了typedef中的初始化`

包含联合体的非打包结构体成员以及打包结构体成员不应分配单独的默认成员值。

当使用数据类型声明没有用户定义 nettype 的线网时，数据类型中的初始赋值表达式将被忽略（见6.7.1）。

## 7.3 联合体
*联合体* 是一种数据类型，它表示可以使用其中一个命名成员数据类型访问的单一存储单元。联合体中的数据类型一次只能使用其中一种。默认情况下，联合体是未打包的，这意味着对于联合体成员的存储表示没有强制要求。动态类型和 chandle 类型只能用于带标签的联合体。

以下 7-2 是联合体声明的语法格式：

---
```verilog
data_type ::= // from A.2.2.1
... 
| struct_union [ packed [ signing ] ] { struct_union_member { struct_union_member } }
{ packed_dimension }13 
struct_union_member16 ::= 
{ attribute_instance } [random_qualifier] data_type_or_void list_of_variable_decl_assignments ;
data_type_or_void ::= data_type | void
struct_union ::= struct | union [ tagged ]
// 13）当使用带有 struct 或 union 关键字的打包维度时，也应使用 packed 关键字。
// 16）只有在标记联合内部才能声明 void struct_union_member。
```
---
语法 7-2——联合体声明语法（摘自附录 A）

例如：
```verilog
typedef union { int i; shortreal f; } num; // 命名联合体
num n; 
n.f = 0.0; // set n in floating point format
typedef struct { 
    bit isfloat; 
    union { int i; shortreal f; } n; // 匿名联合体
} tagged_st; // 命名结构体
```

如果联合体的成员没有指定初始值，则变量将被初始化为联合体类型的声明顺序中第一个成员类型的默认初始值。

为了简化未打包联合体的使用，存在一个特殊规定：如果一个未打包联合体包含几个共享公共初始序列的未打包结构，并且未打包联合体对象当前包含其中一个结构，则允许在任何声明完整类型的联合体可见的地方检查任何一个结构的公共初始部分。如果对应的成员具有等效类型的一个或多个初始成员的序列，则两个结构共享一个公共初始序列。

### 7.3.1 打包联合体
打包联合体只能包含整数数据类型的成员。打包联合体的成员应该是相同大小的（与未打包联合体或打包带标签联合体不同，这些联合体的成员可以是不同大小的）。因此，可以将一个写入的联合体成员作为另一个成员读取。打包联合体也可以作为整体使用算术和逻辑运算符，其行为由 `signed` 或 `unsigned` 关键字确定，后者是默认值。可以像打包数组一样选择打包联合体的一个或多个位，其范围为[n-1:0]。

只有打包数据类型和表 6-8（见6.11）中总结的整数数据类型可以在打包联合体中合法使用。

如果打包联合体包含 2 状态成员和 4 状态成员，则整个联合体是 4 状态的。在读取 2 状态成员时，会发生从 4 状态到 2 状态的隐式转换，而在写入 2 状态成员时，会发生从 2 状态到 4 状态的隐式转换。

例如，联合体可以使用不同的访问宽度：
```verilog
typedef union packed { // 默认无符号
    s_atmcell acell; 
    bit [423:0] bit_slice; 
    bit [52:0][7:0] byte_slice; 
} u_atmcell; 
u_atmcell u1;
byte b; bit [3:0] nib;
b = u1.bit_slice[415:408]; // b = u1.byte_slice[51];
nib = u1.bit_slice [423:420]; // nib = u1.acell.GFC;
```

对于打包联合体，写一个成员并读取另一个成员与机器的字节顺序无关，这与未打包联合体的未打包结构不同，后者是 C 兼容的，成员按地址升序排列。

### 7.3.2 标记联合体
在联合体中使用 `tagged` 声明为 *标记联合体*，使其成为一种类型检查的联合体。普通（未标记）联合体可以使用一个成员类型的值进行更新，并作为另一个成员类型的值读取，这是一种潜在的类型漏洞。标记联合体存储成员值和 *标记*，即表示当前成员名称的附加位。标记和值只能一起一致地使用静态类型检查的标记联合体表达式进行更新（见 11.9）。只能使用与当前标记值（即成员名称）一致的类型读取成员值。因此，不可能存储一个类型的值并（误）将位解释为另一个类型。

动态类型和 chandle 类型不得在未标记联合体中使用，但可以在标记联合体中使用。

标记联合体的成员可以作为标记表达式引用。见 11.9。

除了类型安全性之外，使用成员名称作为标记的使用也使代码比必须跟踪具有显式标记的联合体的代码更简单、更小。标记联合体也可以与模式匹配（见 12.6）一起使用，进一步提高可读性。

在标记联合体中，成员可以声明为 void 类型，当所有信息都在标记本身时，如下面的整数和有效位示例：
```verilog
typedef union tagged {
    void Invalid;
    int Valid;
} VInt;
```

VInt 类型的值是无效的（不包含任何内容）或有效的（包含一个 int）。11.9 描述了如何构造此类型的值，也描述了为何不可能从当前具有 Invalid 标记的 VInt 值中读取整数。

例如：
```verilog
typedef union tagged {
    struct {
        bit [4:0] reg1, reg2, regd;
    } Add;
    union tagged {
        bit [9:0] JmpU;
        struct {
            bit [1:0] cc; 
            bit [9:0] addr;
        } JmpC;
    } Jmp;
} Instr;
```

Instr 类型的值是一个 Add 指令，其中包含三个 5 位寄存器字段，或者是一个 Jmp 指令。在后一种情况下，它要么是无条件跳转，其中包含一个 10 位目的地址，要么是条件跳转，其中包含一个 2 位条件码寄存器字段和一个 10 位目的地址。11.9 描述了如何构造 Instr 类型的值，并描述了如何读取 cc 字段，例如，为了读取 cc 字段，指令必须具有 Jmp 操作码和子操作码 JmpC。

当在标记联合体上使用 packed 限定符时，所有成员都必须具有打包类型，但它们的大小不必相同。打包标记联合体的（标准）表示如下：
- 大小始终等于表示标记所需的位数加上成员的最大大小。
- 标记的大小是编码所有成员名称所需的最小位数（例如，五到八个成员需要 3 个标记位）。
- 标记位始终左对齐（即，朝向 MSB）。
- 对于每个成员，成员位始终右对齐（即，朝向最低有效位（LSB））。
- 标记位和成员位之间的位是未定义的。在 void 成员的极端情况下，只有标记是重要的，所有剩余位都是未定义的。

该表示方案递归地应用于任何嵌套的标记联合体。

例如，如果 VInt 类型定义具有 `packed` 限定符，则 Invalid 和 Valid 值的布局如图 7-1 所示。
![Alt text](Vint.png)
图 7-1 带限定符的 vint 类型

例如，如果 Instr 类型有打包的限定符，它的值将具有如图 7-2 所示的布局。
![Alt text](Instr.png)
图 7-2 带限定符的 Instr 类型

7.3.2 Tagged unions
The qualifier tagged in a union declares it as a tagged union, which is a type-checked union. An ordinary
(untagged) union can be updated using a value of one member type and read as a value of another member
type, which is a potential type loophole. A tagged union stores both the member value and a tag, i.e.,
additional bits representing the current member name. The tag and value can only be updated together
consistently using a statically type-checked tagged union expression (see 11.9). The member value can only
be read with a type that is consistent with the current tag value (i.e., member name). Thus, it is impossible to
store a value of one type and (mis)interpret the bits as another type.
Dynamic types and chandle types shall not be used in untagged unions, but may be used in tagged unions. 
Members of tagged unions can be referenced as tagged expressions. See 11.9. 
In addition to type safety, the use of member names as tags also makes code simpler and smaller than code
that has to track unions with explicit tags. Tagged unions can also be used with pattern matching (see 12.6),
which improves readability even further.
In tagged unions, members can be declared with type void, when all the information is in the tag itself, as in
the following example of an integer together with a valid bit:
typedef union tagged {
void Invalid;
int Valid;
} VInt;
A value of VInt type is either Invalid (and contains nothing) or Valid (and contains an int). Subclause
11.9 describes how to construct values of this type and also describes how it is impossible to read an integer
out of a VInt value that currently has the Invalid tag.
For example:
typedef union tagged {
struct {
bit [4:0] reg1, reg2, regd;
} Add;
union tagged {
bit [9:0] JmpU;
struct {
bit [1:0] cc; 
bit [9:0] addr;
} JmpC;
} Jmp;
} Instr;
A value of Instr type is either an Add instruction, in which case it contains three 5-bit register fields, or it is
a Jmp instruction. In the latter case, it is either an unconditional jump, in which case it contains a 10-bit
destination address, or it is a conditional jump, in which case it contains a 2-bit condition-code register field
and a 10-bit destination address. Subclause 11.9 describes how to construct values of Instr type and
describes how, in order to read the cc field, for example, the instruction must have opcode Jmp and subopcode JmpC.
When the packed qualifier is used on a tagged union, all the members shall have packed types, but they do
not have to be of the same size. The (standard) representation for a packed tagged union is the following:
— The size is always equal to the number of bits needed to represent the tag plus the maximum of the
sizes of the members.
— The size of the tag is the minimum number of bits needed to code for all the member names (e.g.,
five to eight members would need 3 tag bits).
— The tag bits are always left-justified (i.e., towards the MSBs).
— For each member, the member bits are always right-justified [i.e., towards the least significant bits
(LSBs)].
— The bits between the tag bits and the member bits are undefined. In the extreme case of a void member, only the tag is significant and all the remaining bits are undefined.
The representation scheme is applied recursively to any nested tagged unions.
For example, if the VInt type definition had the packed qualifier, Invalid and Valid values will have the
layouts shown in Figure 7-1, respectively. 