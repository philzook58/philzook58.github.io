---
author: philzook58
comments: true
date: 2016-01-16 22:29:02+00:00
layout: post
link: https://www.philipzucker.com/openscad-text-cut/
slug: openscad-text-cut
title: Openscad Text Cut
wordpress_id: 376
---

[http://repraprip.blogspot.com/2011/05/inkscape-to-openscad-dxf-tutorial.html](http://repraprip.blogspot.com/2011/05/inkscape-to-openscad-dxf-tutorial.html)

Need to save as a dxf

In Inkscape convert to path

Then select all nodes and click convert to line and add nodes.

Put it near to 0,0 corner so you can see it.

Save

Put the files in the same place as the scad file



    
    difference() {
    scale([1,1,-1]){
    	import("PoopButton.stl");
    }
    	translate([-16, -5, 5]) {
    scale([.6, .6, .6]){
    		linear_extrude(height = 100, center = true, convexity = 10)
    		import("testtext.dxf");
    }
    	}
    }





