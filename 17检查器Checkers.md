# 17. 检查器
## 17.1 概述
断言提供了验证设计行为的构建块。在许多情况下，需要将几个断言组合成具有明确定义功能的更大块。这些验证块还可能需要包含建模代码，以计算用于断言或与覆盖语句集成的 covergroup 实例的辅助变量的值。SystemVerilog 中的检查器构造专门用于表示这样的验证块，封装了断言以及建模代码。检查器的预期用途是作为验证库单元，或用于创建形式验证中使用的抽象辅助模型的构建块。

检查器中的建模机制类似于模块和接口中的建模机制，尽管存在一些限制。例如，检查器中不能声明和分配任何线网。另一方面，检查器允许非确定性建模，这在模块和接口中不存在。在检查器中声明的每个变量都可以是确定性的或随机的。检查器建模在 17.7 中进行了解释。随机变量对于构建用于形式验证的抽象非确定性模型非常有用。有时，对非确定性模型进行推理比对确定性 RTL 模型进行推理要容易得多。

确定性变量允许断言的常规（确定性）建模。在检查器中使用随机变量而不是常规变量的优点是，同一检查器可以用于确定性和非确定性情况。

## 17.2 检查器声明
---
```verilog
checker_declaration ::= // from A.1.2
checker checker_identifier [ ( [ checker_port_list ] ) ] ;
{ { attribute_instance } checker_or_generate_item } 
endchecker [ : checker_identifier ] 
checker_port_list ::= // from A.1.8
checker_port_item {, checker_port_item}
checker_port_item ::= 
{ attribute_instance } [ checker_port_direction ] property_formal_type formal_port_identifier 
{variable_dimension} [ = property_actual_arg ]
checker_port_direction ::= 
input | output
checker_or_generate_item ::= 
checker_or_generate_item_declaration 
| initial_construct
| always_construct 
| final_construct
| assertion_item
| continuous_assign 
| checker_generate_item
checker_or_generate_item_declaration ::=
[ rand ] data_declaration
| function_declaration 
| checker_declaration 
| assertion_item_declaration
| covergroup_declaration 
| overload_declaration
| genvar_declaration
| clocking_declaration
| default clocking clocking_identifier ;
| default disable iff expression_or_dist ;
| ;
checker_generate_item6 ::= 
loop_generate_construct
| conditional_generate_construct
| generate_region
| elaboration_system_task
checker_identifier ::= // from A.9.3
identifier
// 6) 对于 checker_generate_item 来说，包含在 checker_declaration 外部的任何项都是非法的。
```
---
语法 17-1—检查器声明语法（摘自附录 A）

检查器可以在以下范围内声明：
 - 模块
 - 接口
 - 程序
 - 检查器
 - 包
 - 生成块
 - 编译单元范围

检查器使用关键字 `checker` 后跟名称和可选的形式参数列表声明，并以关键字 `endchecker` 结束。

包含检查器声明的范围中的以下元素不得在检查器中引用：
 - 自动变量和动态变量的成员或元素（参见 6.21）。
 - `fork...join`、`fork...join_any` 或 `fork...join_none` 块的元素。

检查器中断言的动作块将被称为 *检查器动作块*，检查器的其余部分将被称为 *检查器主体*。

检查器主体可以包含以下元素：
 - `let` 构造、序列、属性和函数的声明
 - 延迟断言（参见 16.4）
 - 并发断言（参见 16.14）
 - 检查器声明
 - 其他检查器实例
 - 覆盖组声明和实例
 - 检查器变量声明和赋值（参见 17.7）
 - `default clocking` 和 `default disable iff` 声明
 - `initial`、`always_comb`、`always_latch`、`always_ff` 和 `final` 过程（参见 9.2）
 - 包含上述任何元素的生成块

不得在检查器中声明模块、接口、程序和包。不得在检查器中实例化模块、接口和程序。

检查器的形式参数可以选择由方向限定符 `input` 或 `output` 修饰。如果未显式指定方向，则将推断前一个参数的方向。如果省略了第一个检查器参数的方向，则默认为 `input`。输入检查器形式参数不得由检查器修改。

检查器形式参数的合法数据类型是属性合法的数据类型（参见 16.12）。输出参数的类型不得是 `untyped`、`sequence` 或 `property`。如果省略了检查器形式参数的类型，则根据以下规则推断：
 - 如果参数具有显式方向限定符，则省略其类型将是一个错误。
 - 否则，如果参数是检查器的第一个参数，则假定为 `input untyped`。
 - 否则，将根据序列和属性的描述推断前一个形式参数的类型（参见 16.8 和 16.12）。

与序列和属性类似，检查器声明可以为每个单一输入端口指定默认值，如 16.8 中所述。检查器声明还可以使用与输入参数的默认值规范相同的语法为每个单一输出端口指定初始值。检查器输出端口初始化具有与变量初始化相同的语义（参见 6.8）。

以下是简单检查器的示例：

示例 1：
```verilog
// 包含并发断言的简单检查器
checker my_check1 (logic test_sig, event clock);
    default clocking @clock; endclocking
    property p(logic sig);
        ...
    endproperty
    a1: assert property (p (test_sig));
    c1: cover property (!test_sig ##1 test_sig);
endchecker : my_check1
```

示例 2：
```verilog
// 包含延迟断言的简单检查器
checker my_check2 (logic a, b);
    a1: assert #0 ($onehot0({a, b});
    c1: cover #0 (a == 0 && b == 0);
    c2: cover #0 (a == 1);
    c3: cover #0 (b == 1);
endchecker : my_check2
```

示例 3：
```verilog
// 带有输出参数的简单检查器
checker my_check3 (logic a, b, event clock, output bit failure, undef);
    default clocking @clock; endclocking
    a1: assert property ($onehot0({a, b}) failure = 1’b0; else failure = 1’b1;
    a2: assert property ($isunknown({a, b}) undef = 1’b0; else undef = 1’b1;
endchecker : my_check3
```

示例 4：
```verilog
// 具有默认输入和初始化输出参数的检查器
checker my_check4 (input logic in,
    en = 1’b1, // 默认值
    event clock,
    output int ctr = 0); // 初始值
    default clocking @clock; endclocking
    always_ff @clock
        if (en && in) ctr <= ctr + 1;
    a1: assert property (ctr < 5);
endchecker : my_check4
```

检查器中的类型和数据声明仅在检查器范围内是局部的，并且是静态的。时钟和 `disable iff` 上下文从检查器声明的范围继承（但请参见 17.4，用于使用上下文值函数将实例化上下文传递给检查器的用法）。例如：
```verilog
module m;
    default clocking @clk1; endclocking
    default disable iff rst1;
    checker c1;
    // 继承 @clk1 和 rst1
    ...
    endchecker : c1
    checker c2;
    // 显式重新定义其默认值
    default clocking @clk2; endclocking
    default disable iff rst2;
    ...
    endchecker : c2
    ...
endmodule : m
```

在检查器中使用的变量，既不是检查器的形式参数，也不是检查器的内部变量，将根据从声明检查器的范围中的作用域规则解析。


## 17.3 检查器实例化