# 12. 过程编程语句
## 12.1 概述
本章描述以下内容：
 - 选择语句（if-else，case，casez，casex，unique，unique0，priority）
 - 循环语句（for，repeat，foreach，while，do...while，forever）
 - 跳转语句（break，continue，return）

## 12.2 总览
过程编程语句应包含在以下任一结构中：
 - 自动激活的过程块，以下关键字之一引入：
   - initial
   - always
   - always_comb
   - always_latch
   - always_ff
   - final
   有关每种类型的过程块的描述，请参见第 9 章。
 - 被调用时激活的过程块，以下关键字之一引入：
   - task
   - function
   有关任务和函数的描述，请参见第 13 章。

过程编程语句包括以下内容：
 - 选择语句（请参见 12.4 和 12.5）
 - 循环语句（请参见 12.7）
 - 跳转语句（请参见 12.8）
 - 顺序和并行块（请参见 9.3）
 - 时序控制（请参见 9.4）
 - 过程控制（请参见 9.5 至 9.7）
 - 过程赋值（请参见 10.4 至 10.9）
 - 子程序调用（请参见第 13 章）

## 12.3 语法
过程语句的语法如下 12-1 所示：
---
```verilog
statement_or_null ::= // from A.6.4
statement 
| { attribute_instance } ;
statement ::= [ block_identifier : ] { attribute_instance } statement_item 
statement_item ::= 
blocking_assignment ;
| nonblocking_assignment ;
| procedural_continuous_assignment ;
| case_statement 
| conditional_statement 
| inc_or_dec_expression ;
| subroutine_call_statement 
| disable_statement 
| event_trigger 
| loop_statement 
| jump_statement 
| par_block 
| procedural_timing_control_statement 
| seq_block 
| wait_statement 
| procedural_assertion_statement 
| clocking_drive ;
| randsequence_statement 
| randcase_statement 
| expect_property_statement 
```
---
Syntax 12-1—过程语句语法（摘自附录 A）

## 12.4 条件 if-else 语句
*条件语句*（或 if-else 语句）用于决定是否执行语句。形式上，语法如下 12-2 所示。
---
```verilog
conditional_statement ::= // from A.6.6
[ unique_priority ] if ( cond_predicate ) statement_or_null 
{ else if ( cond_predicate ) statement_or_null } 
[ else statement_or_null ] 
unique_priority ::= unique | unique0 | priority
cond_predicate ::= 
expression_or_cond_pattern { &&& expression_or_cond_pattern } 
expression_or_cond_pattern ::= 
expression | cond_pattern 
cond_pattern ::= expression matches pattern 
```
---
语法 12-2—条件 if-else 语句语法（摘自附录 A）

如果 cond_predicate 表达式计算为真（即，具有非零已知值），则将执行第一个语句。如果它评估为假（即，具有零值或值为 x 或 z），则第一个语句不会执行。如果有 else 语句并且 cond_predicate 表达式为假，则将执行 else 语句。

由于 if 表达式的数值值被测试为零，因此可以进行某些快捷方式。例如，以下两个语句表达相同的逻辑：
```verilog
if (expression)
if (expression != 0)
```

由于 if 的 else 部分是可选的，因此在嵌套的 if 序列中省略 else 时可能会引起混淆。这可以通过始终将 else 与最近的前一个 if 关联来解决，而不带 else。在以下示例中，else 与内部 if 关联，如缩进所示。
```verilog
if (index > 0)
    if (rega > regb)
        result = rega;
    else // else applies to preceding if
        result = regb;
```

如果不希望进行该关联，则应使用 begin-end 块语句来强制执行正确的关联，如以下示例所示。
```verilog
if (index > 0)
    begin
        if (rega > regb)
            result = rega;
    end
else result = regb;
```

### 12.4.1 if-else-if 结构
if-else 结构可以串链。
```verilog
if (expression) statement;
else if (expression) statement;
else if (expression) statement;
else statement;
```

这种 if-else 语句序列（称为 if-else-if 结构）是编写多路决策的最一般方法。表达式将按顺序进行计算。如果任何表达式为真，则将执行与之关联的语句，并且这将终止整个链。每个语句要么是单个语句，要么是一组语句。

if-else-if 结构的最后一个 else 处理没有任何其他条件满足的情况，或者默认情况。有时默认情况没有显式操作。在这种情况下，可以省略尾随 else 语句，或者可以用于错误检查以捕获意外条件。

以下模块片段使用 if-else 语句测试变量 index，以决定是否必须将三个 modify_segn 变量之一添加到内存地址，并且要将哪个增量添加到 index 变量。
```verilog
// 声明变量和参数
logic [31:0] instruction,
             segment_area[255:0];
logic [7:0] index;
logic [5:0] modify_seg1,
            modify_seg2,
            modify_seg3;
parameter
    segment1 = 0, inc_seg1 = 1,
    segment2 = 20, inc_seg2 = 2,
    segment3 = 64, inc_seg3 = 4,
    data = 128;

// 测试 index 变量
if (index < segment2) begin
    instruction = segment_area [index + modify_seg1];
    index = index + inc_seg1;
end
else if (index < segment3) begin
    instruction = segment_area [index + modify_seg2];
    index = index + inc_seg2;
end
else if (index < data) begin
    instruction = segment_area [index + modify_seg3];
    index = index + inc_seg3;
end
else
    instruction = segment_area [index];
```

### 12.4.2 unique-if、unique0-if 和 priority-if
关键字 `unique`、`unique0` 和 `priority` 可以在 `if` 之前使用以执行某些 *违规检查*。

如果使用关键字 `unique` 或 `priority`，如果没有条件匹配，否则将发出 *违规报告*，除非除非有显式的 `else`。例如：
```verilog
unique if ((a==0) || (a==1)) $display("0 or 1");
else if (a == 2) $display("2");
else if (a == 4) $display("4"); // values 3,5,6,7 造成违规报告

priority if (a[2:1]==0) $display("0 or 1");
else if (a[2] == 0) $display("2 or 3");
else $display("4 to 7"); // 覆盖所有其他可能的值，因此不会发出违规报告
```

如果使用关键字 `unique0`，则如果没有条件匹配，不会发生违规。例如：
```verilog
unique0 if ((a==0) || (a==1)) $display("0 or 1");
else if (a == 2) $display("2");
else if (a == 4) $display("4"); // values 3,5,6,7 不会发出违规报告
```

`unique-if` 和 `unique0-if` 断言在一系列 `if-else-if` 条件中没有重叠，即它们是互斥的，因此可以安全地并行评估条件。

在 `unique-if` 和 `unique0-if` 中，条件可以以任何顺序进行计算和比较。实现应在找到真条件后继续评估和比较。如果发现多个条件为真，则 *违反* `unique-if` 或 `unique0-if`。实现应发出违规报告，并执行出现在 `if` 语句中的首个真条件的语句，但不执行与其他真条件相关的语句。

在发现唯一性违规后，实现不需要继续计算和比较其他条件。实现不需要尝试多个条件的评估和比较顺序。条件中的副作用可能导致非确定性结果。

`priority-if` 表示一系列 `if-else-if` 条件应按照列出的顺序进行计算。在前面的示例中，如果变量 a 的值为 0，则它将满足第一个和第二个条件，需要优先逻辑。

`unique`、`unique0` 和 `priority` 关键字适用于整个 `if-else-if` 条件系列。在前面的示例中，在任何 `else` 出现后插入这些关键字是非法的。要在这种条件系列中嵌套另一个 `if` 语句，应使用 `begin-end` 块。

#### 12.4.2.1 由 unique-if、unique0-if 和 priority-if 构造生成的违规报告
12.4.2 中的描述提到了几种情况，其中由 `unique-if`、`unique0-if` 或 `priority-if` 语句生成违规报告。这些违规检查应免于由 active 区域集中的零延迟毛刺导致的虚假违规报告（请参见 4.4.1）。

`unique`、`unique0` 或 `priority` 违规检查在执行语句时进行计算，但违规报告被推迟到当前时间步的 Observed 区域（请参见 4.4）。违规报告可以通过使用断言控制系统任务（请参见 20.12）来控制。

一旦检测到违规，就会在当前时间步的 Observed 区域中安排一个 *待处理的违规报告*。它被调度在与当前执行过程相关联的 *违规报告队列* 上。如果满足以下任一条件，则达到 *违规报告刷新* 点：
 - 由于达到事件控制或等待语句而被暂停的过程恢复执行。
 - 过程由 always_comb 或 always_latch 语句声明，并且由于其依赖信号之一的转换而恢复执行。

如果在过程中达到违规报告刷新点，则其违规报告队列将被清除。任何待处理的违规报告都将被丢弃。

在每个仿真时间步的 Observed 区域中，每个待处理的违规报告应成熟或确认报告。一旦报告成熟，它将不再被刷新。然后使用特定于工具的违规报告机制来报告每个违规，并从适当的过程违规报告队列中清除待处理的违规报告。

以下是一个 `unique-if` 的示例，它免于 active 区域集中的零延迟毛刺：
```verilog
always_comb begin
    not_a = !a;
end

always_comb begin : a1
    u1: unique if (a)
        z = a | b;
    else if (not_a)
        z = a | c;
end
```

在此示例中，`unique if u1` 正在检查两个条件表达式的重叠。当 a 和 not_a 处于 0 和 1 的状态时，a 转换为 1 时，此 `unique if` 可能在 a 和 not_a 都为真的情况下执行，因此唯一性检查将失败。由于此检查在 active 区域集中，因此不会立即报告失败。在更新 not_a 后，将重新调度过程 a1，这将导致刷新原始违规报告。现在，违规检查将通过，不会报告任何违规。

另一个示例显示了循环结构同样免于 active 区域集中的零延迟毛刺：
```verilog
always_comb begin
    for (int j = 0; j < 3; j++)
        not_a[j] = !a[j];
end

always_comb begin : a1
    for (int j = 0; j < 3; j++) 
        unique if (a[j])
            z[j] = a[j] | b[j];
        else if (not_a[j])
            z[j] = a[j] | c[j];
end
```

此示例与前一个示例相同，但添加了循环语句。每个循环迭代以与前一个示例完全相同的方式独立检查唯一性违规。循环中的任何迭代都可以报告唯一性违规。如果重新调度过程 a1，则所有违规将被刷新，并且整个循环将被重新评估。

#### 12.4.2.2 if 语句违规报告和多个过程
如前面的章节所述（参见 12.4.2 和 12.4.2.1），违规报告与执行它们的过程相关联。这意味着在任务或函数中的违规检查可能会由于任务或函数被多个不同过程调用而被执行多次，而每个这些不同的过程执行是独立的。以下示例说明了这种情况：
```verilog
module fsm(...);
    function bit f1(bit a, bit not_a, ...)
        ...
        a1: unique if (a)
            ...
        else if (not_a)
            ...
    endfunction
    ...
    always_comb begin : b1
        some_stuff = f1(c, d, ...);
        ...
    end
    always_comb begin : b2
        other_stuff = f1(e, f, ...);
        ...
    end
endmodule
```

在这种情况下，有两个不同的过程可能调用过程 a1:b1 和 b2。假设仿真在第一个时间步的 active 区域中执行以下场景。请注意，此示例涉及仿真时间中的三个不同点以及如何处理每个特定时间步的毛刺解决方案：
 - `a)` 在时间步 1 中，b1 执行 c=1 和 d=1，b2 执行 e=1 和 f=1。在第一个时间步中，由于 a1 在 b1 和 b2 过程中独立失败，因此其失败报告会报告两次。
 - `b)` 在时间步 2 中，b1 执行 c=1 和 d=1，然后再次执行 c=1 和 d=0。在第二个时间步中，当重新触发过程时，b1 中的 a1 失败被刷新，因此最终执行通过，不会报告任何失败。
 - `c)` 在时间步 3 中，b1 执行 c=1 和 d=1，然后 b2 执行 e=1 和 f=0。在第三个时间步中，b1 中的失败没有看到刷新点，因此会报告该失败。在 b2 中，违规检查通过，因此不会报告任何失败。

## 12.5 case 语句
*case* 语句是一个多路决策语句，用于测试表达式是否与其他表达式中的一个匹配，并相应地分支。case 语句的语法如下 12-3 所示。
---
```verilog
case_statement ::= // from A.6.7
[ unique_priority ] case_keyword ( case_expression )
case_item { case_item } endcase
| [ unique_priority ] case_keyword (case_expression )matches
case_pattern_item { case_pattern_item } endcase
| [ unique_priority ] case ( case_expression ) inside
case_inside_item { case_inside_item } endcase
case_keyword ::= case | casez | casex
case_expression ::= expression 
case_item ::= 
case_item_expression { , case_item_expression } : statement_or_null 
| default [ : ] statement_or_null 
case_pattern_item ::= 
pattern [ &&& expression ] : statement_or_null 
| default [ : ] statement_or_null 
case_inside_item ::= 
open_range_list : statement_or_null 
| default [ : ] statement_or_null 
case_item_expression ::= expression 
```
---
语法 12-3—case 语句语法（摘自附录 A）

`default` 语句是可选的。在一个 case 语句中使用多个 default 语句是非法的。

`case_expression` 和 `case_item_expressions` 不需要是常量表达式。

case 语句的一个简单示例是解码变量数据以生成 result 值，如下所示：
```verilog
logic [15:0] data;
logic [9:0] result;

case (data)
    16'd0: result = 10'b0111111111;
    16'd1: result = 10'b1011111111;
    16'd2: result = 10'b1101111111;
    16'd3: result = 10'b1110111111;
    16'd4: result = 10'b1111011111;
    16'd5: result = 10'b1111101111;
    16'd6: result = 10'b1111110111;
    16'd7: result = 10'b1111111011;
    16'd8: result = 10'b1111111101;
    16'd9: result = 10'b1111111110;
    default result = 'x;
endcase
```

`case_expression` 将被精确计算一次，并且在任何 `case_item_expressions` 之前。`case_item_expressions` 将被计算，然后按照它们出现的确切顺序进行比较。如果有一个 default `case_item`，则在此线性搜索期间将忽略它。在线性搜索期间，如果 `case_item_expressions` 中的一个与 `case_expression` 匹配，则将执行与该 `case_item` 关联的语句，并且线性搜索将终止。如果所有比较失败并且给出了 default `case_item`，则将执行 `default` `case_item` 语句。如果未给出 `default` 语句并且所有比较失败，则不会执行任何 `case_item` 语句。

除了语法之外，case 语句与多路 if-else-if 结构在两个重要方面有所不同：
 - if-else-if 结构中的条件表达式比在 case 语句中将一个表达式与其他表达式进行比较更通用。
 - case 语句在表达式中存在 x 和 z 值时提供了明确的结果。

在 case_expression 比较中，只有当每个位与 0、1、x 和 z 值相匹配时，比较才会成功。因此，在指定 case 语句中的表达式时需要小心。所有表达式的位长度需要相等，以便可以执行精确的位匹配。因此，所有 `case_item_expressions` 的长度，以及 `case_expression` 的长度，应该等于最长的 `case_expression` 和 `case_item_expressions` 的长度。如果这些表达式中的任何一个是无符号的，则所有这些表达式都应被视为无符号的。如果所有这些表达式都是有符号的，则应将它们视为有符号的。

提供处理 x 和 z 值的 case_expression 比较的原因是它提供了一种检测这些值并减少由其存在引起的悲观情况的机制。

例1：以下示例说明了使用 case 语句正确处理 x 和 z 值的方法：
```verilog
case (select[1:2])
    2'b00: result = 0;
    2'b01: result = flaga;
    2'b0x,
    2'b0z: result = flaga ? 'x : 0;
    2'b10: result = flagb;
    2'bx0,
    2'bz0: result = flagb ? 'x : 0;
    default result = 'x;
endcase
```

在此示例中，如果 `select[1]` 为 0 并且 flaga 为 0，则即使 `select[2]` 的值为 x 或 z，result 应为 0，这由第三个 `case_item` 解决。

例2：以下示例显示了另一种使用 case 语句检测 x 和 z 值的方法：
```verilog
case (sig)
    1'bz: $display("signal is floating");
    1'bx: $display("signal is unknown");
    default: $display("signal is %b", sig);
endcase
```

### 12.5.1 带有不关心条件的 case 语句
提供了两种 case 语句，以允许在 case 比较中处理不关心条件。其中一种将高阻值（z）视为不关心，另一种将高阻值和未知（x）值视为不关心。这些 case 语句可以与传统 case 语句一样使用，但它们以关键字 `casez` 和 `casex` 开头。

在这些 case 语句中，`case_expression` 或 `case_items` 中的任意比特不关心值（casez 的 z 值，casex 的 z 和 x 值）在比较中被视为不关心条件，并且该位位置不会被考虑。

字面数值的语法允许在 case 语句中使用问号（?）代替 z。这提供了一种方便的格式，用于在 case 语句中指定不关心位。

例1：以下是 casez 语句的示例。它演示了指令解码，其中 ir 的 MSB 的值选择应调用哪个任务。如果 ir 的 MSB 为 1，则调用指令 1，而不管 ir 的其他位的值如何。
```verilog
logic [7:0] ir;

casez (ir)
    8'b1???????: instruction1(ir);
    8'b01??????: instruction2(ir);
    8'b00010???: instruction3(ir);
    8'b000001??: instruction4(ir);
endcase
```

例2：以下是 casex 语句的示例。它演示了如何在仿真期间动态控制不关心条件的极端情况。在此示例中，如果 r = 8'b01100110，则调用任务 stat2。
```verilog
logic [7:0] r, mask;

mask = 8'bx0x0x0x0;
casex (r ^ mask)
    8'b001100xx: stat1;
    8'b1100xx00: stat2;
    8'b00xx0011: stat3;
    8'bxx010100: stat4;
endcase
```

### 12.5.2 case 语句中的常量表达式
常量表达式可以用于 case_expression。常量表达式的值将与 case_item_expressions 进行比较。

以下示例演示了通过建模 3 位优先级编码器来使用的常量表达式：
```verilog
logic [2:0] encode;

case (1)
    encode[2]: $display("Select Line 2");
    encode[1]: $display("Select Line 1");
    encode[0]: $display("Select Line 0");
    default $display("Error: One of the bits expected ON");
endcase
```

在此示例中，case_expression 是一个常量表达式（1）。case_items 是表达式（位选择），并与常量表达式进行比较以进行匹配。

### 12.5.3 unique-case、unique0-case 和 priority-case
case、casez 和 casex 关键字可以由 priority、unique 或 unique0 关键字限定，以执行某些 *违规检查*。这些统称为 priority-case、unique-case 或 unique0-case。priority-case 应仅对第一个匹配执行。unique-case 和 unique0-case 断言没有重叠的 case_items，因此可以安全地并行计算 case_items。

在 unique-case 和 unique0-case 中，case_expression 应在任何 case_item_expressions 之前且仅计算一次。case_item_expressions 可以按任何顺序计算和比较。实现应在找到匹配 case_expression 的 case_item 后继续计算和比较。如果发现多个 case_item 匹配 case_expression，则 *违反* unique-case 和 unique0-case。实现应发出违规报告，并执行出现在 case 语句中的首个匹配 case_item 的语句，但不执行与其他匹配 case_item 相关的语句。

在发现唯一性违规后，实现不需要继续计算和比较其他 case_items。单个 case_item 包含多个与 case_expression 匹配的 case_item_expression 不会违反唯一性。如果 case_item_expression 与 case_expression 匹配，则实现不需要在同一 case_item 中计算其他 case_item_expressions。实现不需要尝试多个 case_item_expressions 的计算和比较顺序。case_item_expressions 中的副作用可能导致非确定性结果。

如果 case 限定为 priority 或 unique，则仿真器应在没有 case_item 匹配时发出违规报告。如果可能的话，编译时可能会发出违规报告。如果在编译时无法确定违规，则应在运行时发出违规报告。如果 case 限定为 unique0，则实现不应在没有 case_item 匹配时发出违规报告。

注意：通过指定 unique 或 priority，不需要编写默认 case 来捕获意外 case 值。

考虑以下示例：
```verilog
bit [2:0] a;
unique case(a) // values 3,5,6,7 造成违规报告
    0, 1: $display("0 or 1");
    2: $display("2");
    4: $display("4");
endcase

priority casez(a) // values 4,5,6,7 造成违规报告
    3'b00?: $display("0 or 1");
    3'b0??: $display("2 or 3");
endcase

unique0 case(a) // values 3,5,6,7 不会发出违规报告
    0, 1: $display("0 or 1");
    2: $display("2");
    4: $display("4");
endcase
```

#### 12.5.3.1 由 unique-case、unique0-case 和 priority-case 构造生成的违规报告
12.5.3 中的描述提到了几种情况，其中由 unique-case、unique0-case 或 priority-case 语句生成违规报告。这些违规检查应免于由 active 区域集中的零延迟毛刺导致的虚假违规报告（请参见 4.4.1）。违规报告可以通过使用断言控制系统任务（请参见 20.12）来控制。

在处理零延迟毛刺的机制应与处理 unique-if、unique0-if 和 priority-if 构造时使用的机制相同（请参见 12.4.2.1）。

以下是一个 unique-case 的示例，它免于 active 区域集中的零延迟毛刺：
```verilog
always_comb begin
    not_a = !a;
end

always_comb begin : a1
    unique case (1'b1) 
        a : z = b;
        not_a : z = c;
    endcase
end
```

在此示例中，unique case 正在检查两个 case_item 选择的重叠。当 a 和 not_a 处于 0 和 1 的状态时，a 转换为 1 时，此 unique case 可能在 a 和 not_a 都为真的情况下执行，因此唯一性检查将失败。由于此检查在 active 区域集中，因此不会立即报告失败。在更新 not_a 后，将重新调度过程 a1，这将导致刷新原始违规报告。现在，违规检查将通过，不会报告任何违规。

#### 12.5.3.2 case 语句违规报告和多个过程
case 违规报告与执行它们的过程相关联，与 if 违规报告处理相同。

### 12.5.4 集合成员 case 语句
关键字 `inside` 可以在括号表达式后使用，以指示集合成员（参见 11.4.13）。在 *case-inside* 语句中，case_expression 应使用集合成员 inside 运算符与每个 case_item_expression（open_range_list）进行比较。inside 运算符使用非对称通配符匹配（见 11.4.6）。因此，case_expression 应是左操作数，每个 case_item_expression 应是右操作数。case_expression 和每个 case_item_expression 中的大括号中的表达式应按照正常 case、unique-case 或 priority-case 语句指定的顺序进行计算。当 inside 操作将 case_expression 与 case_item_expressions 进行比较并返回 1'b1 时，case_item 将匹配，并且当操作返回 1'b0 或 1'bx 时不匹配。如果所有比较都不匹配并且给出了默认项，则将执行默认项语句。

例如：
```verilog
logic [2:0] status;
always @(posedge clock)
    priority case (status) inside
    1, 3 : task1; // 匹配 'b001 和 'b011
    3'b0?0, [4:7]: task2; // 匹配 'b000 'b010 'b0x0 'b0z0 'b100 'b101 'b110 'b111
    endcase // priority case 失败对于  'b00x 'b01x 'bxxx
```

## 12.6 模式匹配条件表达式
模式匹配提供了一种可视化和简洁的表示法，用于比较值与结构、标记联合和常量，并访问其成员。模式匹配可以与 case 和 if-else 语句以及条件表达式一起使用。在描述这些上下文中的模式匹配之前，首先描述一般概念。

模式是一个标记联合和结构表达式的嵌套，其中包含标识符、常量表达式（请参见 11.2.1）和叶子处的通配符模式 “`.*`”。对于标记联合模式，跟在 tagged 关键字后面的标识符是联合成员名称。对于 void 成员，嵌套成员模式被省略。
---
```verilog
pattern ::= // from A.6.7.1
. variable_identifier 
| .*
| constant_expression 
| tagged member_identifier [ pattern ] 
| '{ pattern { , pattern } }
| '{ member_identifier : pattern { , member_identifier : pattern } }
```
---
语法 12-4—模式语法（摘自附录 A）

模式总是出现在已知类型的上下文中，因为它与已知类型的表达式进行匹配。递归地，其嵌套模式也具有已知类型。常量表达式模式应为整数类型。因此，模式总是可以进行静态类型检查的。

每个模式引入一个新的作用域；该作用域的范围将在下面分别为 case 语句、if-else 语句和条件表达式描述。每个模式标识符在模式的作用域内隐式声明为一个新变量，其类型基于其在模式中的位置而唯一确定。模式标识符在模式中应该是唯一的，即在单个模式中不能使用相同的标识符。

在模式匹配中，表达式的值 V 总是与模式进行匹配，并且静态类型检查验证 V 和模式具有相同的类型。模式匹配的结果如下：
 - 一个 1 位确定值：0（false，或失败）或 1（true，或成功）。结果不能是 x 或 z，即使值和模式包含这样的位。
 - 如果匹配成功，则模式标识符绑定到 V 中的相应成员值，使用普通的过程赋值。
 - 每个模式都使用以下简单递归规则进行匹配：
   - 标识符模式总是成功（匹配任何值），并且标识符绑定到该值（使用普通的过程赋值）。
   - 通配符模式 “`.*`” 总是成功。
   - 常量表达式模式成功，如果 V 等于其值。
   - 标记联合模式成功，如果值具有相同的标记，并且递归地，如果嵌套模式匹配标记联合的成员值。
   - 结构模式成功，如果递归地每个嵌套成员模式匹配 V 中的相应成员值。在具有命名成员的结构模式中，成员的文本顺序不重要，成员可以省略。省略的成员将被忽略。

从概念上讲，如果将值 V 视为位的扁平化向量，则模式指定要匹配的位，以及应该匹配的值，如果匹配成功，则应该提取并绑定到模式标识符的位。匹配可以对 x 和 z 值不敏感，如下面的各个构造所述。

### 12.6.1 case 语句中的模式匹配
在模式匹配 case 语句中，表达式在括号中，后面跟着关键字 matches，然后是一系列 case_pattern_items。case 项的左侧，在冒号（`:`）之前，由 *模式* 组成，可选地由运算符 `&&&` 后跟一个布尔过滤 *表达式*。case 项的右侧是一个语句。每个模式引入一个新的作用域，在该作用域中，其模式标识符隐式声明；此作用域延伸到同一 case 项中的可选过滤表达式和右侧语句。因此，不同的 case 项可以重用模式标识符。

所有模式都经过完全静态类型检查。在模式匹配 case 语句中的被测表达式应具有已知类型，该类型与每个 case 项中的模式的类型相同。

在模式匹配 case 语句中的表达式应该被精确计算一次。它的值 V 应该与给定的顺序一次匹配 case 项的左侧，忽略默认 case 项（如果有）。在此线性搜索期间，如果选择了一个 case 项，则执行其语句，并终止线性搜索。如果没有选择 case 项，并且给出了默认 case 项，则执行其语句。如果没有选择 case 项，并且没有给出默认 case 项，则不执行任何语句。

为了选择 case 项，值 V 应该匹配模式（模式标识符被赋予相应的成员值），然后布尔过滤表达式应该计算为 true（确定值，非 0）。

例1：
```verilog
typedef union tagged {
    void Invalid;
    int Valid;
} VInt;
...
VInt v;
...
case (v) matches
    tagged Invalid : $display ("v is Invalid");
    tagged Valid .n : $display ("v is Valid with value %d", n);
endcase
```

在 case 语句中，如果 v 当前具有 Invalid 标记，则匹配第一个模式。否则，它必须具有 Valid 标记，然后匹配第二个模式。标识符 n 绑定到 Valid 成员的值，并显示此值。当标记为 Invalid 时，无法访问整数成员值（n）。

例2：
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
...
Instr instr;
...
case (instr) matches
    tagged Add '{.r1, .r2, .rd} &&& (rd != 0) : rf[rd] = rf[r1] + rf[r2]; 
    tagged Jmp .j : case (j) matches
        tagged JmpU .a : pc = pc + a;
        tagged JmpC '{.c, .a}: if (rf[c]) pc = a;
    endcase
endcase
```

如果 instr 包含 Add 指令，则匹配第一个模式，并且标识符 r1、r2 和 rd 绑定到嵌套结构值中的三个寄存器字段。右侧语句执行寄存器文件 rf 上的指令。如果标记为 Jmp，访问这些寄存器字段是不可能的。如果 instr 包含 Jmp 指令，则匹配第二个模式，并且标识符 j 绑定到嵌套标记联合值。内部 case 语句依次将此值与 JmpU 和 JmpC 模式匹配，依此类推。

例3（与前一个示例相同，但使用通配符和常量模式来消除 rd = 0 的情况；在某些处理器中，寄存器 0 是特殊的“丢弃”寄存器）：
```verilog
case (instr) matches
    tagged Add '{.*, .*, 0} : ; // no op 
    tagged Add '{.r1, .r2, .rd} : rf[rd] = rf[r1] + rf[r2];
    tagged Jmp .j : case (j) matches
        tagged JmpU .a : pc = pc + a;
        tagged JmpC '{.c, .a} : if (rf[c]) pc = a;
    endcase
endcase
```

例4（与前一个示例相同，但第一个内部 case 语句仅涉及结构和常量，但没有标记联合）：
```verilog
case (instr) matches
    tagged Add s: case (s) matches
        '{.*, .*, 0} : ; // no op 
        '{.r1, .r2, .rd} : rf[rd] = rf[r1] + rf[r2];
    endcase
    tagged Jmp .j: case (j) matches
        tagged JmpU .a : pc = pc + a;
        tagged JmpC '{.c, .a} : if (rf[c]) pc = a;
    endcase
endcase
```

例5（与前一个示例相同，但使用嵌套标记联合模式）：
```verilog
case (instr) matches
    tagged Add '{.r1, .r2, .rd} &&& (rd != 0) : rf[rd] = rf[r1] + rf[r2]; 
    tagged Jmp (tagged JmpU .a) : pc = pc + a;
    tagged Jmp (tagged JmpC '{.c, .a}) : if (rf[c]) pc = a;
endcase
```

例6（与前一个示例相同，但使用命名结构成员）：
```verilog
case (instr) matches
    tagged Add '{reg2:.r2,regd:.rd,reg1:.r1} &&& (rd != 0): 
        rf[rd] = rf[r1] + rf[r2];
    tagged Jmp (tagged JmpU .a) : pc = pc + a;
    tagged Jmp (tagged JmpC '{addr:.a,cc:.c}) : if (rf[c]) pc = a;
endcase
```

casez 和 casex 关键字可以用于替代 case，具有相同的语义。换句话说，在模式匹配期间，无论比较的是 2 位（无论它们是标记位还是成员），casez 形式都会忽略 z 位，而 casex 形式会忽略 z 和 x 位。

priority 和 unique 限定符也可以使用。priority 意味着必须选择某个 case 项。unique 意味着必须选择某个 case 项，并且还意味着将选择某个 case 项，因此它们可以并行计算。

### 12.6.2 if 语句中的模式匹配
在 if-else 语句中，谓词可以是一系列用 `&&&` 运算符分隔的子句。每个子句可以是一个表达式（用作布尔过滤器）或具有形式：*表达式 matches 模式*。子句表示从左到右的顺序连接（即，如果任何子句失败，则不会计算剩余子句），并且所有子句都必须成功才能使谓词为 true。布尔表达式子句按照通常的方式进行计算。每个模式引入一个新的作用域，在该作用域中，其模式标识符隐式声明；此作用域延伸到谓词的剩余子句和 if-else 语句的相应“true”分支。

在每个 e matches p 子句中，e 和 p 应该有相同的已知为静态的已知类型。e 的值与前面描述的模式 p 进行匹配。

尽管模式匹配子句总是返回一个定义的 1 位结果，但由于谓词中的布尔过滤表达式，整体结果可能是模棱两可的。if-else 语句的标准语义适用，即如果且仅当结果是确定值而不是 0 时，才执行第一个语句。

例1：
```verilog
if (e matches (tagged Jmp (tagged JmpC '{cc:.c,addr:.a})))
    ... // c 和 a 可以在这里使用
else
    ...
```

例2（与前一个示例相同，说明了两个模式匹配的序列，其中第一个模式中绑定的标识符在第二个模式中使用）：
```verilog
if (e matches (tagged Jmp .j) &&& 
    j matches (tagged JmpC '{cc:.c,addr:.a}))
    ... // c 和 a 可以在这里使用
else
    ...
```

例3（与第一个示例相同，但在谓词序列中添加了一个布尔表达式）。表达的想法是“如果 e 是条件跳转指令且条件寄存器不等于零...”。
```verilog
if (e matches (tagged Jmp (tagged JmpC '{cc:.c,addr:.a}))
    &&& (rf[c] != 0)) 
    ... // c 和 a 可以在这里使用
else
    ...
```

priority 和 unique 限定符也可以使用，即使它们使用模式匹配。

### 12.6.3 条件表达式中的模式匹配
条件表达式（e1 ? e2 : e3）也可以使用模式匹配，即谓词 e1 可以是一系列用 `&&&` 运算符分隔的表达式和子句，就像 if-else 语句的谓词一样。每个子句表示从左到右的顺序连接（即，如果任何子句失败，则不会计算剩余子句），并且所有子句都必须成功才能使谓词为 true。布尔表达式子句按照通常的方式进行计算。每个模式引入一个新的作用域，在该作用域中，其模式标识符隐式声明；此作用域延伸到谓词的剩余子句和随后的 e2。

如前所述，e1 可以计算为 true、false 或模棱两可的值。根据这三种可能的结果，11.4.11 描述了条件表达式的标准语义。

## 12.7 循环语句
SystemVerilog 提供了六种类型的循环结构，如语法 12-5 所示。
---
```verilog
loop_statement ::= // from A.6.8
forever statement_or_null 
| repeat ( expression ) statement_or_null 
| while ( expression ) statement_or_null 
| for ( [ for_initialization ] ; [ expression ] ; [ for_step ] ) 
statement_or_null 
| do statement_or_null while ( expression ) ;
| foreach ( ps_or_hierarchical_array_identifier [ loop_variables ] ) statement 
for_initialization ::= 
list_of_variable_assignments 
| for_variable_declaration { , for_variable_declaration } 
for_variable_declaration ::= 
[ var ] data_type variable_identifier = expression { , variable_identifier = expression }14
for_step ::= for_step_assignment { , for_step_assignment } 
for_step_assignment ::= 
operator_assignment 
| inc_or_dec_expression 
| function_subroutine_call 
loop_variables ::= [ index_variable_identifier ] { , [ index_variable_identifier ] } 
// 14) 当在 net 声明中使用 type_reference 时，应在其前面加上 net 类型关键字；当在变量声明中使用 type_reference 时，应在其前面加上 var 关键字。
```
---
语法 12-5—循环语句语法（摘自附录 A）

### 12.7.1 for 循环
*for 循环* 通过三步过程控制其关联语句的执行，如下所示：
 - a）除非省略了可选的 for_initialization，否则执行一个或多个 for_initialization 赋值，通常用于初始化控制循环执行次数的变量。
 - b）除非省略了可选的表达式，否则计算表达式。如果结果为 false（如 12.4 中定义），则 for 循环将退出。否则，或者如果省略了表达式，则 for 循环将执行其关联语句，然后执行步骤 c）。如果表达式计算结果为未知或高阻值，则应将其视为零。
 - c）除非省略了可选的 for_step，否则执行一个或多个 for_step 赋值，通常用于修改循环控制变量的值，然后重复步骤 b）。

用于控制 for 循环的变量可以在循环之前声明。如果两个或多个并行进程中的循环使用相同的循环控制变量，则有一个潜在的问题，即一个循环在其他循环仍在使用该变量时修改该变量。

用于控制 for 循环的变量也可以在循环内部声明，作为 for_initialization 赋值的一部分。这在循环周围创建了一个隐式的 begin-end 块，包含循环变量的声明，其生命周期为自动。此块创建了一个新的分层作用域，使变量局部于循环作用域。默认情况下，该块未命名，但可以通过向 for 循环语句添加语句标签（9.3.5）来命名。因此，其他并行循环不能无意中影响循环控制变量。例如：
```verilog
module m;

    initial begin
        for (int i = 0; i <= 255; i++)
        ...
    end

    initial begin
        loop2: for (int i = 15; i >= 0; i--)
        ...
    end

endmodule
```

这等效于以下内容：
```verilog
module m;

    initial begin
        begin
            automatic int i;
            for (i = 0; i <= 255; i++) 
            ...
        end
    end

    initial begin
        begin : loop2
            automatic int i;
            for (i = 15; i >= 0; i--)
            ...
        end
    end

endmodule
```

只有在 for_initialization 赋值的一部分中包含变量声明的 for 循环语句才会在其周围创建隐式的 begin-end 块。

初始声明或赋值语句可以是一个或多个逗号分隔的语句。步骤赋值也可以是一个或多个逗号分隔的赋值语句、增量或减量表达式或函数调用。
```verilog
for ( int count = 0; count < 3; count++ )
    value = value +((a[count]) * (count+1));

for ( int count = 0, done = 0, j = 0; j * count < 125; j++, count++)
    $display("Value j = %d\n", j );
```

在 for 循环初始化中，控制变量的所有或无一应在本地声明。在上面的示例中，count、done 和 j 都是本地声明的。以下是非法的，因为它尝试本地声明 y，而 x 没有本地声明：
```verilog
for (x = 0, int y = 0; ...)
...
```

在声明多个本地变量的 for 循环初始化中，本地变量的初始化表达式可以使用先前的本地变量。
```verilog
for (int i = 0, j = i+offset; i < N; i++,j++)
...
```

### 12.7.2 repeat 循环
*repeat 循环* 执行一个语句固定次数。如果表达式计算结果为未知或高阻值，则应将其视为零，没有语句将被执行。

在以下 repeat 循环示例中，add 和 shift 运算符实现了一个乘法器：
```verilog
parameter size = 8, longsize = 16;
logic [size:1] opa, opb;
logic [longsize:1] result;

begin : mult
    logic [longsize:1] shift_opa, shift_opb;
    shift_opa = opa;
    shift_opb = opb;
    result = 0;
    repeat (size) begin
        if (shift_opb[1])
            result = result + shift_opa;
        shift_opa = shift_opa << 1;
        shift_opb = shift_opb >> 1;
    end
end
```

### 12.7.3 foreach 循环
*foreach 循环* 用于迭代数组的元素。参数是一个标识符代表任何类型的数组，后面跟着一个方括号括起来的逗号分隔的循环变量列表。每个循环变量对应于数组的一个维度。foreach 循环和 repeat 循环类似，使用数组边界来指定循环次数而不是表达式。

示例：
```verilog
string words [2] = '{ "hello", "world" };
int prod [1:8] [1:3];

foreach( words [ j ] )
    $display( j , words[j] ); // 打印每个索引和值

foreach( prod[ k, m ] )
    prod[k][m] = k * m; // 初始化
```

循环变量的数量不得大于数组变量的维数。循环变量可以省略以指示不迭代该数组的维度，并且循环变量列表中的尾随逗号也可以省略。与 for 循环（12.7.1）类似，foreach 循环在循环语句周围创建一个隐式的 begin-end 块，包含具有自动生存期的循环变量的声明。此块创建了一个新的分层作用域，使变量局部于循环作用域。默认情况下，该块未命名，但可以通过向 foreach 语句添加语句标签来命名（9.3.5）。foreach 循环变量是只读的。每个循环变量的类型隐式声明为与数组索引类型一致。循环变量的标识符不能与数组相同。

循环变量到数组索引的映射由维度基数决定，在 20.7 中描述。foreach 循环安排更高的基数索引改变更快。

```verilog
//     1  2  3         3    4       1   2 -> 维度数
int A [2][3][4]; bit [3:0][2:1] B [5:1][4]; 

foreach( A [ i, j, k ] ) ...
foreach( B [ q, r, , s ] ) ...
```

在第一个 foreach 循环中，i 从 0 到 1，j 从 0 到 2，k 从 0 到 3。在第二个 foreach 循环中，q 从 5 到 1，r 从 0 到 3，s 从 2 到 1（跳过第三个索引的迭代）。

如果在 foreach 循环的执行过程中更改了动态大小数组的维数，则结果是未定义的，并且可能导致生成无效的索引值。

多个循环变量对应于嵌套循环，这些循环对给定的索引进行迭代。循环的嵌套由维度基数决定；外部循环对应于较低基数索引。在上面的第一个示例中，最外层循环对应于 i，最内层循环对应于 k。

当循环变量用于除作为指定数组的索引之外的表达式时，它们会自动转换为与索引类型一致的类型。对于固定大小和动态大小数组，自动转换类型为 int。对于由特定索引类型索引的关联数组，自动转换类型为与索引类型相同的类型。要使用不同的类型，可以使用显式转换。

### 12.7.4 while 循环
*while 循环* 重复执行一个语句，只要控制表达式为真（12.4 中定义）。如果表达式在 while 循环开始时不为真，则语句将不会执行。

以下示例计算 data 中的逻辑 1 值的数量：
```verilog
begin : count1s
    logic [7:0] tempreg;
    count = 0;
    tempreg = data;
    while (tempreg) begin
        if (tempreg[0])
            count++;
        tempreg >>= 1;
    end
end
```

### 12.7.5 do...while 循环
*do...while 循环* 与 while 循环不同，它在循环体执行之后测试控制表达式。在结束进行测试有时候是有用的以便在循环体中避免重复的代码。
```verilog
string s;
if ( map.first( s ) )
    do
        $display( "%s : %d\n", s, map[ s ] );
    while ( map.next( s ) );
```

条件可以是任何可以作为布尔值处理的表达式。它在语句之后计算。

### 12.7.6 forever 循环
*forever 循环* 重复执行一个语句。为了避免零延迟无限循环，可能会挂起仿真事件调度器，forever 循环应该只与时间控制或 disable 语句一起使用。例如：
```verilog
initial begin
    clock1 <= 0;
    clock2 <= 0;
    fork
        forever #10 clock1 = ~clock1;
        #5 forever #10 clock2 = ~clock2;
    join
end
```

## 12.8 跳转语句
---
```verilog
jump_statement ::= // from A.6.5
return [ expression ] ;
| break ;
| continue ;
```
---
语法 12-6—跳转语句语法（摘自附录 A）

SystemVerilog 提供了类似 C 的跳转语句 break、continue 和 return。
```verilog
break // 退出循环，与 C 中的 break 相同
continue // 跳到循环的末尾，与 C 中的 continue 相同
return expression // 退出函数
return // 退出任务或 void 函数
```

continue 和 break 语句只能在循环中使用。continue 语句跳到循环的末尾并执行循环控制（如果存在）。break 语句跳出循环。

continue 和 break 语句不能在 fork-join 块中使用以控制块外的循环。

return 语句只能在子例程中使用。在返回值的函数中，return 语句应具有正确类型的表达式。

注意：SystemVerilog 不包括 C 中的 goto 语句。
