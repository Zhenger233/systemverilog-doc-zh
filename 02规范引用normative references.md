# 2. 规范引用

下列引用文件对于本标准的应用是必不可少的（即它们必须被理解和使用，因此每个参考文件在文中被引用，并对其与本文件的关系进行了解释。 对于注明日期的参考文献，仅适用于引用的版本。 对于未注明日期的参考资料，适用于最新版本的参考文件（包括任何修正案或勘误表）。

## Anderson, R., Biham, E., and Knudsen, L. “Serpent: A Proposal for the Advanced Encryption Standard,”NIST AES Proposal, 1998.

Serpent 是一种对称密钥分组密码，曾入围高级加密标准 (AES) 竞赛的决赛，在比赛中仅次于 Rijndael。Serpent 由 Ross Anderson、Eli Biham 和 Lars Knudsen 设计。与其他 AES 提交一样，Serpent 的块大小为 128 位，并支持 128、192 或 256 位的密钥大小。 [4] 密码是一个 32 轮替换-排列网络，在一个由四个 32 位字组成的块上运行。 每轮并行应用八个 4 位到 4 位 S 盒中的一个 32 次。 Serpent 的设计使得所有操作都可以使用 32 位片并行执行。 这最大限度地提高了并行性，但也允许使用在 DES 上执行的大量密码分析工作。

## ANSI X9.52-1998, American National Standard for Financial Services—Triple Data Encryption Algorithm Modes of Operation.

**三重数据加密算法**，缩写为TDEA，Triple DEA，或称 **3DES**（Triple DES），是一种[对称密钥加密](https://baike.baidu.com/item/%E5%AF%B9%E7%A7%B0%E5%AF%86%E9%92%A5%E5%8A%A0%E5%AF%86?fromModule=lemma_inlink)块密码，相当于是对每个数据块应用三次[数据加密标准](https://baike.baidu.com/item/%E6%95%B0%E6%8D%AE%E5%8A%A0%E5%AF%86%E6%A0%87%E5%87%86?fromModule=lemma_inlink)（DES）算法。由于计算机运算能力的增强，原版DES密码的[密钥长度](https://baike.baidu.com/item/%E5%AF%86%E9%92%A5%E9%95%BF%E5%BA%A6?fromModule=lemma_inlink)变得容易被[暴力破解](https://baike.baidu.com/item/%E6%9A%B4%E5%8A%9B%E7%A0%B4%E8%A7%A3?fromModule=lemma_inlink)；3DES即是设计用来提供一种相对简单的方法，即通过增加DES的密钥长度来避免类似的攻击，而不是设计一种全新的块密码算法。

## ElGamal, T., “A Public-Key Cryptosystem and a Signature Scheme Based on Discrete Logarithms,” IEEE Transactions on Information Theory, vol. IT-31, no. 4, pp. 469–472, July 1985.

门限加密算法提出了一种新的签名方案，并实现了Diffie-Hellman密钥分发方案，实现了公钥密码系统。 这两个系统的安全性都依赖于有限域上离散对数的计算难度。

## FIPS 46-3 (October 1999), Data Encryption Standard (DES).

**数据加密标准**是一种[对称密钥加密](https://zh.wikipedia.org/wiki/%E5%B0%8D%E7%A8%B1%E5%AF%86%E9%91%B0%E5%8A%A0%E5%AF%86 "对称密钥加密")[块密码](https://zh.wikipedia.org/wiki/%E5%A1%8A%E5%AF%86%E7%A2%BC "块密码")算法，1976年被[美国](https://zh.wikipedia.org/wiki/%E7%BE%8E%E5%9B%BD "美国")联邦政府的[国家标准局](https://zh.wikipedia.org/wiki/%E5%9B%BD%E5%AE%B6%E6%A0%87%E5%87%86%E5%B1%80 "国家标准局")确定为[联邦资料处理标准](https://zh.wikipedia.org/wiki/%E8%81%94%E9%82%A6%E8%B5%84%E6%96%99%E5%A4%84%E7%90%86%E6%A0%87%E5%87%86 "联邦资料处理标准")（FIPS），随后在国际上广泛流传开来。它基于使用56位密钥的[对称算法](https://zh.wikipedia.org/w/index.php?title=%E5%AF%86%E9%92%A5%E5%AF%86%E7%A0%81%E5%AD%A6&action=edit&redlink=1 "密钥密码学（页面不存在）")。这个算法因为包含一些[机密](https://zh.wikipedia.org/wiki/%E6%A9%9F%E5%AF%86 "机密")设计元素，相对短的[密钥长度](https://zh.wikipedia.org/wiki/%E5%AF%86%E9%92%A5%E9%95%BF%E5%BA%A6 "密钥长度")以及怀疑内含[美国国家安全局](https://zh.wikipedia.org/wiki/%E7%BE%8E%E5%9C%8B%E5%9C%8B%E5%AE%B6%E5%AE%89%E5%85%A8%E5%B1%80 "美国国家安全局")（NSA）的[后门](https://zh.wikipedia.org/wiki/%E5%90%8E%E9%97%A8 "后门")而在开始时有争议，DES因此受到了强烈的学院派式的审查，并以此推动了现代的[块密码](https://zh.wikipedia.org/wiki/%E5%A1%8A%E5%AF%86%E7%A2%BC "块密码")及其[密码分析](https://zh.wikipedia.org/wiki/%E5%AF%86%E7%A0%81%E5%88%86%E6%9E%90 "密码分析")的发展。

## FIPS 180-2 (August 2002), Secure Hash Standard (SHS).

安全哈希标准指定了四种安全哈希算法——SHA-1、SHA-256、SHA-384和SHA-512——用于计算电子数据(消息)的压缩表示。 当任何长度< 264位(对于SHA-1和SHA-256)或< 2128位(对于SHA-1和SHA-256)的消息
 SHA-384和SHA-512是算法的输入，结果是称为消息摘要的输出。 消息摘要的长度范围从160位到512位，具体取决于算法。 安全哈希算法通常与其他加密算法一起使用，例如数字签名算法和密钥哈希消息验证码，或者用于生成随机数(位)。

## FIPS 197 (November 2001), Advanced Encryption Standard (AES).

高级加密标准AES (Advanced Encryption Standard)是美国国家标准与技术研究院(NIST)于2001年制定的电子数据加密规范。
 
 AES是Rijndael分组密码的变体，由两位比利时密码学家Joan Daemen和Vincent Rijmen开发，他们在AES选择过程中向NIST提交了提案。Rijndael是一组具有不同密钥和块大小的密码。 对于AES, NIST选择了Rijndael家族的三个成员，每个成员的块大小为128位，但有三种不同的密钥长度:128位、192位和256位。

## IEEE Std 754™, IEEE Standard for Floating-Point Arithmetic.

IEEE浮点算术标准(IEEE 754)是由电气与电子工程师协会(IEEE)于1985年建立的浮点算术技术标准。 该标准解决了在各种浮点实现中发现的许多问题，这些问题使它们难以可靠和可移植地使用。 许多硬件浮点单元使用IEEE 754标准。

## IEEE Std 1003.1™, IEEE Standard for Information Technology—Portable Operating System Interface (POSIX®).

可移植操作系统接口是由IEEE计算机学会指定的一系列标准，用于维护操作系统之间的兼容性。POSIX定义了系统级和用户级应用程序编程接口(api)，以及命令行外壳和实用程序接口，以实现与Unix和其他操作系统变体的软件兼容性(可移植性)。POSIX也是IEEE.的商标，旨在供应用程序和系统开发人员使用。

## IEEE Std 1364™-1995, IEEE Standard Hardware Description Language Based on the Verilog® Hardware Description Language.

IEEE Std 1364™-1995定义了Verilog硬件描述语言(HDL)。 Verilog HDL是一种正式的符号，用于电子系统创建的所有阶段。 因为它既是机器可读的，也是人类可读的，它支持硬件设计的开发、验证、综合和测试; 硬件设计数据的沟通; 以及硬件的维护、改造和采购。 该标准的主要受众是支持该语言的工具的实现者和该语言的高级用户。

## IEEE Std 1364™-2001, IEEE Standard Verilog Hardware Description Language.

IEEE Std 1364™-2001取代1364 - 1995。 该标准定义了Verilog硬件描述语言HDL (Hardware Description Language)。 Verilog HDL是一种正式的符号，用于电子系统创建的所有阶段。 因为它既是机器可读的，也是人类可读的，它支持硬件设计的开发、验证、综合和测试; 硬件设计数据的沟通; 以及硬件的维护、改造和采购。 该标准的主要受众是支持该语言的工具的实现者和该语言的高级用户。

## IEEE Std 1364™-2005, IEEE Standard for Verilog Hardware Description Language.

IEEE Std 1364™-2005标准中定义了Verilog硬件描述语言(HDL)。 Verilog HDL是一种正式的符号，用于电子系统创建的所有阶段。 因为它是机器可读的和人类可读的，它支持硬件设计的开发、验证、综合和测试; 硬件设计数据的沟通; 以及硬件的维护、改造和采购。 该标准的主要受众是支持该语言的工具的实现者和该语言的高级用户。 (取代IEEE Std 1364-2001。 被IEEE Std 1800-2009取代)。

## IEEE Std 1800™-2005, IEEE Standard for SystemVerilog—Unified Hardware Desiggn, Specification, and Verification Language.

IEEE Std 1800™-2005标准融合了IEEE 1364-2005 Verilog硬件描述语言(HDL)和IEEE 1800-2005 SystemVerilog统一硬件设计、规范和验证语言。 2005 SystemVerilog标准定义了对2005 Verilog标准的扩展。 这两种标准被设计成一种语言使用。 将基本Verilog语言和SystemVerilog扩展合并到一个标准中，用户可以在一个文档中获得有关语法和语义的所有信息。

## IEEE Std 1800™-2009, IEEE Standard for SystemVerilog—Unified Hardware Design, Specification, and Verification Language.

IEEE Std 1800™-2009标准代表了之前两个标准的合并:IEEE Std 1364-2005 Verilog硬件描述语言(HDL)和IEEE Std 1800-2005 SystemVerilog统一硬件设计、规范和验证语言。 2005 SystemVerilog标准定义了对2005 Verilog标准的扩展。 这两种标准被设计成一种语言使用。 将基本Verilog语言和SystemVerilog扩展合并到一个标准中，用户可以在一个文档中获得有关语法和语义的所有信息。

## IETF RFC 1319 (April 1992), The MD2 Message-Digest Algorithm.

IETF RFC 1319描述了MD2消息摘要算法。 该算法将任意长度的消息作为输入，并将输入的128位“指纹”或“消息摘要”作为输出。 据推测，产生具有相同消息摘要的两个消息，或产生具有给定预先指定的目标消息摘要的任何消息，在计算上是不可行的。 MD2算法适用于数字签名应用程序，在使用公钥加密系统(如RSA)下的私钥(秘密)对大文件进行签名之前，必须以安全的方式“压缩”。

## IETF RFC 1321 (April 1992), The MD5 Message-Digest Algorithm.

IETF RFC 1321介绍MD5消息摘要算法。 该算法将任意长度的消息作为输入，并将输入的128位“指纹”或“消息摘要”作为输出。 据推测，产生具有相同消息摘要的两个消息，或产生具有给定预先指定的目标消息摘要的任何消息，在计算上是不可行的。 MD5算法适用于数字签名应用程序，在使用公钥加密系统(如RSA)下的私钥(秘密)加密之前，必须以安全的方式“压缩”大文件。
IETF RFC 2045 (November 1996), Multipurpose Internet Mail Extensions (MIME), Part One: Format of Internet Message Bodies.

STD 11, RFC 822定义了一个消息表示协议，指定了关于US-ASCII消息头的大量细节，并将消息内容(或消息体)保留为普通的US-ASCII文本。这组文档被统称为多用途Internet邮件扩展(Multipurpose Internet Mail Extensions，简称MIME)，它们重新定义了消息的格式

(1)非US-ASCII字符集的文本消息体，
(2)针对非文本消息体的可扩展的不同格式集;
(3)多部分消息体
(4)非US-ASCII字符集的文本头信息。
RFC2045文档基于RFC 934、STD 11和RFC 1049中记录的早期工作，但对它们进行了扩展和修订。由于RFC 822对消息体的描述很少，这些文档在很大程度上与RFC 822正交(而不是RFC 822的修订版)。

这个文档指定了用于描述MIME消息结构的各种报头。第二个文档RFC 2046定义了MIME媒体类型系统的一般结构，并定义了一组初始的媒体类型。第三个文档RFC 2047描述了对RFC 822的扩展，以允许在Internet邮件报头字段中使用非us - ascii文本数据。第四份文件RFC 2048规定IANA对mime相关设施的各种注册程序。第五个也是最后一个文档RFC 2049描述了MIME一致性标准，以及提供MIME消息格式，确认，和书目的一些说明性的例子。

这个文档是rfc 1521、1522和1590的修订本，而rfc 1521、1522和1590本身是rfc 1341和1342的修订本。RFC 2049的附录描述了与以前版本的差异和变化。

## IETF RFC 2144 (May 1997), The CAST-128 Encryption Algorithm.

Internet社区需要一种无阻碍的加密算法，该算法具有一系列密钥大小，可以为各种加密应用程序和协议提供安全性。
IETF RFC 2144描述了一种现有的算法，可以用来满足这一需求。 包括密码和密钥调度算法的描述(第2节)，s盒(附录a)，和一组测试向量(附录B)。

## IETF RFC 2437 (October 1998), PKCS #1: RSA Cryptography Specifications, Version 2.0.

IETF RFC 2437是RFC 2313的后续版本。本文档提供了基于RSA算法的公钥密码学实现建议，包括以下几个方面:
 加密原语
 加密方案
 带附录的签名方案
 表示键和标识方案的asn.1语法

## IETF RFC 2440 (November 1998), OpenPGP Message Format.

维护本文档的目的是发布开发基于OpenPGP格式的可互操作应用程序所需的所有必要信息。 它不是编写应用程序的按部就班的食谱。 它只描述了读取、检查、生成和写入跨越任何网络的符合要求的数据包所需的格式和方法。 它不处理存储和实现问题。 但是，本文讨论了避免安全缺陷所必需的实现问题。
 Open-PGP软件使用强公钥和对称密码学的组合，为电子通信和数据存储提供安全服务。 这些服务包括机密性、密钥管理、身份验证和数字签名。 本文档指定了OpenPGP中使用的消息格式。

## ISO/IEC 10118-3:2004, Information technology—Security techniques—Hash-functions—Part 3: Dedicated hash-functions.

ISO/IEC 10118-3:2004指定了以下7个专用哈希函数，即专门设计的哈希函数:
 
 第7条中的第一个哈希函数(RIPEMD-160)提供长度不超过160位的哈希码;
 第8条中的第二个哈希函数(RIPEMD-128)提供长度不超过128位的哈希码;
 第9条中的第三个哈希函数(SHA-1)提供长度不超过160位的哈希码;
 第10条中的第四个哈希函数(SHA-256)提供长度不超过256位的哈希码;
 第11条中的第五个哈希函数(SHA-512)提供长度不超过512位的哈希码;
 第12条中的第6个哈希函数(SHA-384)提供固定长度的384位哈希码; 而且
 第13条中的第7个哈希函数(WHIRLPOOL)提供长度不超过512位的哈希码。
 对于这些专用的哈希函数，ISO/IEC 10118-3:2004指定了一个轮函数，它由一系列子函数、填充方法、初始化值、参数、常量和对象标识符组成，作为规范信息，还指定了几个计算示例作为信息信息。

## Schneier, B., “Description of a New Variable-Length Key, 64-Bit Block Cipher (Blowfish),” Fast Software Encryption, Cambridge Security Workshop Proceedings (December 1993), Springer-Verlag, 1994, pp. 191–204.

提出了一种新的秘钥分组密码——圆函数blowfish。这是一个Feistel网络，迭代一个简单的加密函数16次。块大小为64位，密钥可以是任何长度，最大可达448位。尽管在进行任何加密之前需要一个复杂的初始化阶段，但在大型微处理器上，数据的实际加密是非常有效的。

## Schneier, B., et al., The Twofish Encryption Algorithm: A 128-Bit Block Cipher, 1st ed., Wiley, 1999.

Twofish是一种128位的分组密码，可接受256位的变长密钥。 该密码是一个16轮Feistel网络，其双射F函数由4个密钥依赖的8 × 8位s盒、GF(28)上固定的4 × 4最大距离可分离矩阵、伪hadamard变换、位旋转和精心设计的密钥调度组成。奔腾Pro上完全优化的Twofish实现以每字节17.8个时钟周期进行加密，8位智能卡实现以每字节1660个时钟周期进行加密。 Twofish可以在14000个门的硬件中实现。 轮函数和键调度的设计允许在速度、软件大小、键设置时间、门数和内存之间进行各种各样的权衡。
