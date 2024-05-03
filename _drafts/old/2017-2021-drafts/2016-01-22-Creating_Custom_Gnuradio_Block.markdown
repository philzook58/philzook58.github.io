---
author: philzook58
comments: true
date: 2016-01-22 01:30:48+00:00
layout: post
link: https://www.philipzucker.com/?p=375
published: false
slug: Creating Custom Gnuradio Block
title: Creating Custom Gnuradio Block
wordpress_id: 375
---

gr_modtool create testblock


gr_modtool add -t sync -l python




when it asks for variable, give comma delimitted list




edit python file




    
    class copy_ff(gr.sync_block):
        """
        docstring for block copy_ff
        """
        def __init__(self, add, multiply=1):
            self.multiply = multiply
            self.add = add
            gr.sync_block.__init__(self,
                name="copy_ff",
                in_sig=[numpy.float32],
                out_sig=[numpy.float32])
    
    
        def work(self, input_items, output_items):
            in0 = input_items[0]
            out = output_items[0]
            # <+signal processing here+>
            #out[:] = in0
            out[:] = in0*self.multiply+ self.add
            return len(output_items[0])


Most of that is template. Make sure to set the variables to self in the init and also change the in and out types to something.


edit xml file in grc folder




    
    <code>mkdir build
    cd build
    cmake ../
    make
    sudo make install
    sudo ldconfig</code>


I had an import error. I think it might be because I use different pythons for different things. I can import testblock in regular python. It was fixed by adding


export PYTHONPATH=/usr/local/lib/python2.7/site-packages:$PYTHONPATH




to my .bashrc
