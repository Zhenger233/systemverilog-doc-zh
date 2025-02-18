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
  




