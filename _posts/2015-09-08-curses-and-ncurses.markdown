---
author: philzook58
comments: true
date: 2015-09-08 19:36:36+00:00
layout: post
link: https://www.philipzucker.com/curses-and-ncurses/
slug: curses-and-ncurses
title: Curses and Ncurses or whatevs.
wordpress_id: 125
---

So I was wondering how to make slightly less wonky command line programs. Sometimes they aren't. Like top or nano or vi and stuff.

I think the answer is curses,

I basically read this

[https://docs.python.org/2/howto/curses.html](https://docs.python.org/2/howto/curses.html)

Here's a short example program that I think sort of demonstrates enough to get you going.

Press q to quit

z, r, and p do stuff.

Very curious that you have to do this sequence of build up and tear down or else it freaks. Ctrl-c does exits nicely due to that bit of code about signals. Ctrl-c send SIGINT signal

    
    import curses
    stdscr = curses.initscr()
    curses.start_color()
    curses.noecho()
    curses.cbreak()
    stdscr.keypad(1)
    
    
    import signal
    import sys
    def signal_handler(signal, frame):
       curses.nocbreak(); stdscr.keypad(0); curses.echo()
       curses.endwin()
       print('You pressed Ctrl+C!')
       sys.exit(0)
    signal.signal(signal.SIGINT, signal_handler)
    
    begin_x = 20; begin_y = 7
    height = 5; width = 40
    win = curses.newwin(height, width, begin_y, begin_x)
    
    #curses.init_pair(1, curses.COLOR_RED, curses.COLOR_WHITE)
    
    while 1:
        c = stdscr.getch()
        if c == ord('p'):
            stdscr.addstr("Pretty text", curses.color_pair(0))
            stdscr.refresh()
        elif c == ord('q'):
            break  # Exit the while()
        elif c == curses.KEY_HOME:
            x = y = 0
        elif c == ord('r'):
            stdscr.addstr(0, 0, "Current mode: Typing mode",
                  curses.A_REVERSE)
            stdscr.refresh()
        elif c == ord('z'):
            stdscr.addstr(20, 20, "I AM YOUR GOD",
                  curses.A_BLINK)
            stdscr.refresh()
    
    curses.nocbreak(); stdscr.keypad(0); curses.echo()
    curses.endwin()
    



