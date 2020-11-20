---
author: philzook58
comments: true
date: 2015-10-30 17:58:11+00:00
layout: post
link: https://www.philipzucker.com/svg-to-c-data-using-python/
slug: svg-to-c-data-using-python
title: SVG to C data using python
wordpress_id: 214
---

So, we've been building a little servo mechanism to move a mirror to aim a laser (a super fast and hacky hot glue job on a 2x4, but dang dong if it don't basically work) and I thought it'd be nice to write a little script that converts paths in svg files (which I can draw in inkscape)  into a C struct that we can just stick into an arduino file and read from. If anybody else needs this, you'll need to modify some stuff. All the stuff is cobbled together from stackexchange replies. God, I love python. Checkout the nice little float regular expression.

    
    from xml.dom import minidom
    
    #Suggestion:python svgwrite.py mysvg >> outputfile
    # append a bunch of images to file
    
    import sys
    if len(sys.argv) < 2:
        print "***** USAGE: python svgparse.py filename *****"
    
    svg_file = sys.argv[1]
    
    doc = minidom.parse(svg_file)  # parseString also exists
    path_strings = [path.getAttribute('d') for path
                    in doc.getElementsByTagName('path')]
    doc.unlink()
    #print path_strings
    
    import re
    posStrings = re.findall(r"[-+]?\d*\.\d+|\d+", path_strings[0])
    
    x = []
    y = []
    for i in range(len(posStrings)):
        if i % 2 == 0:
            x.append(float(posStrings[i]))
        else:
            y.append(float(posStrings[i]))
    
    '''
    print "x"
    print x
    print "y"
    print y
    '''
    
    # Insert math here. Normalization, centering, etc. precomputation of angles.
    
    #print svg_file.split('.')[0]
    
    print "float xpos[" + str(len(x)) + "] = {" + ", ".join(map(str,x)) + "};"
    print "float ypos[" + str(len(y)) + "] = {" + ", ".join(map(str,y)) + "};"
    



