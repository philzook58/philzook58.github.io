---
author: philzook58
comments: true
date: 2020-11-06 19:08:24+00:00
layout: post
link: https://www.philipzucker.com/?p=1159
published: false
slug: Automatic Differentiation in Verilog
title: Automatic Differentiation in Verilog
wordpress_id: 1159
---

I'm back on the case a little

I'm going to try nmigen. I like python. 

Eventually I figured out i really do need to install the full icestorm tool chain from source. It actually isn't hard. Literally copy and paste the instructions from the icestorm website. Trying to use any apt installed versions is going to cause you pain. They don't seem to be up to date (although I am on Ubuntu 18.04 which is old now).

Something confusing. It looks like the most modern development of nmigen occurs not in the easiest to find github repo 

  * [https://github.com/nmigen/nmigen](https://github.com/nmigen/nmigen)
  * https://nmigen.info/nmigen/latest/intro.html
  * https://nmigen.info/nmigen/latest/tutorial.html

7/2018

That the GADT instance will hide the held types is gonna kill me. I guess that is fine if it holds the code itself?

Should I just write some verilog?

    
    module Add(x, y, z, dx, dy, dz)
    input [0:26] x;
    input [0:26] y;
    output [0:26] z;
    input [0:26] dz;
    output [0:26] dx;
    output [0:26] dy;
    
    assign dx = dz;
    assign dy = dz;
    assign z = x + y;
    
    endmodule

 

    
    data VerilogTypes = VBit VBit | BV BitVec | Arr VerilogTypes 
    
    data Module input output = Module {mname :: String, minput :: [VerilogTypes], moutput :: [VerilogTypes], code :: String} |
    						   Comp Module Module | Id
    
    --data Comp k a b where
    --	Comp :: VerilogEntity b => k b c -> k a b -> 
    
    
    
    
    data VBit = VBit {bname :: String}
    
    data BitVec = BitVec {bvname :: String}
    
    bv = BitVec
    
    add :: Module (BitVec, BitVec) BitVec
    add = Module "Add" (BitVec "x", BitVec "y") (BitVec "z")
    
    dup :: Module a (a,a)
    dup = Module "Dup" (BitVec "x", BitVec "y") (BitVec "z")
    
    
    newtype ADModule x y dx dy = ADModule (Module (x,dy) (y,dx))
    
    
    gen (Comp m1 m2) = newWires <- mapM getFresh (outputs m2)
    				   set (inputs m1) newWires
    gen (Module mname minput moutput) =
    
    
    outputs (Comp Id m2) = outputs m2
    outputs (Comp m1 _) = outputs m1
    outputs (Module _ _ o) = o
    
    inputs (Comp m1 m2) = inputs m2
    inputs (Comp m1 m2) = inputs m2
    inputs (Module _ i _) = i
    
    
    getFreshWire :: String -> State GenState VerilogVar
    getFreshWire x = do
    	   (used,code) <- read
    	   newname = head filter (\s -> notin s used) (map (x ++ show) [0 ..])
    	   newused = newname : used
    	   newcode = code ++ "wire " ++ newname ++ ";\n"
    	   put (newused, newcode)
    	   return newname
    
    getFreshMod ::

 
