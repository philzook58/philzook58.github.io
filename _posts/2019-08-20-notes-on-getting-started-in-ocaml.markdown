---
author: philzook58
comments: true
date: 2019-08-20 01:21:43+00:00
layout: post
link: https://www.philipzucker.com/notes-on-getting-started-in-ocaml/
slug: notes-on-getting-started-in-ocaml
title: Notes on Getting Started in OCaml
wordpress_id: 2052
categories:
- Haskell
tags:
- ocaml
---




I know a bit of Haskell. It's the functional programming language I have the strongest background in. OCaml is very similar to Haskell, which is why I haven't felt a strong need to learn it. Having had to delve into it for necessity because of work I think that was an oversight. The biggest thing for me is being able to more easily read a new set of literature and see familiar things in a new light, which is very refreshing.







### Getting OCaml







[https://ocaml.org/docs/install.html](https://ocaml.org/docs/install.html)







opam is the package manager. Follow the instructions to install it and get your environment variables setup. It'll tell you some extra commands you have to run to do so. You use it to install packages via `opam install packagename`. You can also use it to switch between different ocaml compiler versions via command like `opam switch 4.08.1`. 







Dune is a build tool. You can place a small config file called `dune` in your  folder and it can figure out how to appropriately call the compiler. Dune is in flux, so check out the documentation. What I write here may be wrong.







[https://dune.readthedocs.io/en/stable/](https://dune.readthedocs.io/en/stable/)







Here's an example execution. Note that even though the file is called `main.ml` in this example, you call build with `main.exe`. And exec requires the `./` for some reason. Weird.






    
    <code>dune init exe hello
    dune exec ./main.exe
    dune build main.exe
    </code>







Here's a dune file with some junk in it. You make executables with blocks. You include a list of the files without the .ml suffix require by the executable in the modules line. You list libraries needed in the libraries line.






    
    <code>(executable
     (name main)
     (modules ("main"))
     (libraries core z3 owl owl-plplot)
     )
    
     (executable 
      (name lambda)
      (modules ("lambda"))
      (libraries core)
     )</code>







You want to also install merlin. `opam install merlin`. Merlin is a very slick IDE tool with autocomplete and type information.  dune will setup a .merlin file for you 







The ReasonML plugin is good for vscode. Search for it on the marketplace. It is the one for OCaml also. ReasonML is a syntactic facelift intended for the web btw. I don't particularly recommend it to start. There are also emacs and vim modes if that is what you're into.







The enhanced repl is called utop. Install it with `opam install utop`. Basic repl usage: Every line has to end with `;;`.  That's how you get stuff to be run. Commands start with `#`. For example `#quit;;` is how you end the session. `#use "myfile.ml";;` will load a file you've made. Sometimes when you start you need to run `#use "topfind";;` which loads a package finder. You can load libraries via the require command like `#require "Core";;`







`#help;;` for more.







### A Quick Look at the Language







With any new language I like to check out Learn X from Y if one is available.







[https://learnxinyminutes.com/docs/ocaml/](https://learnxinyminutes.com/docs/ocaml/)







Here are some shortish cheat sheets with a quick overview of syntax







[https://github.com/alhassy/OCamlCheatSheet](https://github.com/alhassy/OCamlCheatSheet)







[https://ocaml.org/docs/cheat_sheets.html](https://ocaml.org/docs/cheat_sheets.html)







### More In Depth Looks







This is a phenomenal book online book built for a Cornell course: [https://www.cs.cornell.edu/courses/cs3110/2019sp/textbook/](https://www.cs.cornell.edu/courses/cs3110/2019sp/textbook/)







[Real World OCaml](http://dev.realworldocaml.org/) is also quite good but denser. Very useful as a reference for usage of Core and other important libraries.







The reference manual is also surprisingly readable [https://caml.inria.fr/pub/docs/manual-ocaml/](https://caml.inria.fr/pub/docs/manual-ocaml/) . The first 100 or so pages are a straightforward introduction to the language.







[https://github.com/janestreet/learn-ocaml-workshop](https://github.com/janestreet/learn-ocaml-workshop) Pretty basic workshop. Could be useful getting you up and running though.







### Useful libraries







Core - a standard library replacement. Becoming increasingly common [https://github.com/janestreet/core](https://github.com/janestreet/core) It is quite a bit more confusing for a newcomer than the standard library IMO. And the way they have formatted their docs is awful.







Owl - a numerical library. Similar to Numpy in many ways. [https://ocaml.xyz/](https://ocaml.xyz/) These tutorials are clutch [https://github.com/owlbarn/owl/wiki](https://github.com/owlbarn/owl/wiki)







[Bap -](https://github.com/BinaryAnalysisPlatform/bap) Binary Analysis Platform. Neato stuff







Lwt - [https://github.com/ocsigen/lwt](https://github.com/ocsigen/lwt) asynchronous programming







Graphics - gives you some toy and not toy stuff. Lets you draw lines and circles and get keyboard events in a simple way.







OCamlGraph - a graph library







[Jupyter Notebook](https://github.com/akabe/ocaml-jupyter) - Kind of neat. I've got one working on binder. Check it out here. [https://github.com/philzook58/ocaml_binder](https://github.com/philzook58/ocaml_binder)







Menhir and OCamlLex. Useful for lexer and parser generators. Check out the ocaml book for more







fmt -  for pretty printing







### Interesting Other Stuff (A Descent into Lazy Writing)







[https://discuss.ocaml.org/](https://discuss.ocaml.org/) - The discourse. Friendly people. They don't bite. Ask questions.







[https://github.com/ocaml-community/awesome-ocaml](https://github.com/ocaml-community/awesome-ocaml) Awesome-Ocaml list. A huge dump of interesting libraries and resources.







An excerpt of cool stuff:







  * [Coq](https://coq.inria.fr/) – Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs.
  * [Why3](http://why3.lri.fr/) – Why3 is a platform for deductive program verification. It provides a rich language for specification and programming, called WhyML, and relies on external theorem provers, both automated and interactive, to discharge verification conditions.
  * [Alt-Ergo](http://alt-ergo.lri.fr/) – Alt-Ergo is an open-source SMT solver dedicated to the proof of mathematical formulas generated in the context of program verification.






[http://ocamlverse.github.io/](http://ocamlverse.github.io/) - A pretty good set of beginner advice and articles. Seems like I have a lot of accidental overlap. Would've been nice to find earlier







[https://www.cl.cam.ac.uk/teaching/1617/L28/materials.html](https://www.cl.cam.ac.uk/teaching/1617/L28/materials.html) - advanced functional programming course. Interesting material.







TAPL - [https://www.cis.upenn.edu/~bcpierce/tapl/](https://www.cis.upenn.edu/~bcpierce/tapl/) Has implementations in OCaml of different lambda calculi. Good book too.







It is not uncommon to use a preprocessor in OCaml for some useful features. There is monad syntax, list comprehensions, deriving and more available as ppx extensions.







[https://whitequark.org/blog/2014/04/16/a-guide-to-extension-points-in-ocaml/](https://whitequark.org/blog/2014/04/16/a-guide-to-extension-points-in-ocaml/) ppx perepsorcssor. ocamlp4 5 are both preprocessors too







[https://tarides.com/blog/2019-05-09-an-introduction-to-ocaml-ppx-ecosystem.html](https://tarides.com/blog/2019-05-09-an-introduction-to-ocaml-ppx-ecosystem.html)







[https://blog.janestreet.com/archive/](https://blog.janestreet.com/archive/) The jane street blog. They are very prominent users of ocaml.







[https://opensource.janestreet.com/standards/](https://opensource.janestreet.com/standards/) Jane Street style guide








https://youtu.be/QDXfKXi_Q_A








Oleg Kiselyov half works in Haskell, half in OCaml, so that's cool.







[https://arxiv.org/pdf/1905.06544.pdf](https://arxiv.org/pdf/1905.06544.pdf) oleg effects without monads







Oleg metaocaml book. MetaOCaml is super cool. [http://okmij.org/ftp/ML/MetaOCaml.html](http://okmij.org/ftp/ML/MetaOCaml.html) And the switch funtionality of opam makes it easy to install!







Oleg tagless final [http://okmij.org/ftp/tagless-final/index.html](http://okmij.org/ftp/tagless-final/index.html)







[https://github.com/ocamllabs/higher](https://github.com/ocamllabs/higher)







Cohttp, LWT and Async







[https://github.com/backtracking/ocamlgraph](https://github.com/backtracking/ocamlgraph) ocaml graphs







[https://mirage.io/](https://mirage.io/) Mirage os. What the hell is this?







[https://github.com/ocamllabs/fomega](https://github.com/ocamllabs/fomega)







[https://github.com/janestreet/hardcaml](https://github.com/janestreet/hardcaml)







ppx_let monaidc let bindings







some of the awesome derivinig capabilites are given by ppx_jane. SExp seems to be a realy good one. It's where generic printing is?







`dune build lambda.bc.js` will make a javascript file. That's pretty cool. Uses js_of_ocaml. The js_of_ocaml docs are intimidating  [https://ocsigen.org/js_of_ocaml/dev/manual/overview](https://ocsigen.org/js_of_ocaml/dev/manual/overview)







[http://ocsigen.org/js_of_ocaml/dev/api/](http://ocsigen.org/js_of_ocaml/dev/api/)







Note you need to install both the js_of_ocaml-compiler AND the library js_of_ocaml and also the js_of_ocaml-ppx.












    
    <code>(executable
     (name jsboy)
     (libraries js_of_ocaml)
     (preprocess (pps js_of_ocaml-ppx))
     )</code>






    
    <code>open Js_of_ocaml
    let _ =
      Js.export "myMathLib"
        (object%js
           method add x y = x +. y
           method abs x = abs_float x
           val zero = 0.
         end)</code>







Go digging through your _build folder and you can find a completely mangled incomprehensible file `jsboy.bc.js`. But you can indeed import and use it like so.






    
    <code>var mystuff = require("./jsboy.bc.js").myMathLib;
    console.log(mystuff)
    console.log(mystuff.add(1,2))</code>






    
    <code>node test.js</code>







`dune build --profile release lambda.bc.js` putting it in the release profile makes an insane difference in build size. 10mb -> 100kb







There is also bucklescript for compiling to javascript. Outputs readable javascript. Old compiler fork?







Check out J.T. Paach's snippets. Helpful







Dune:







[https://gist.github.com/jtpaasch/ce364f62e283d654f8316922ceeb96db](https://gist.github.com/jtpaasch/ce364f62e283d654f8316922ceeb96db)







Z3 ocaml







[https://gist.github.com/jtpaasch/3a93a9e1bcf9cae86e9e7f7d3484734b](https://gist.github.com/jtpaasch/3a93a9e1bcf9cae86e9e7f7d3484734b)







Ocaml new monadic let syntax







[https://jobjo.github.io/2019/04/24/ocaml-has-some-new-shiny-syntax.html](https://jobjo.github.io/2019/04/24/ocaml-has-some-new-shiny-syntax.html)






    
    <code></code>







#require "ppx_jane";; in utop in order to import a thing using ppx







And argument could be made for working from a docker







Weird dsls that generate parsers and lexers. Also oddly stateful.







Took a bit of fiddling to figure out how to get dune to do.






    
    <code> (executable
     (name lisp)
     (modules ("lisp" "parse_lisp" "lex_lisp" "ast"))
     (preprocess (pps  ppx_jane))
     (libraries core)
     )
    
    (ocamllex
      (modules lex_lisp))
    
    (menhir
     
     (modules parse_lisp))</code>







Otherwise pretty straight forward encoding



















expereince rport: using f omega as a teaching language







Because they aren't hidden behind a monadic interface (for better or for worse), OCaml has a lot more of imperative feel. You could program in a subset of the language and have it not feel all that different from Java or python or something. There are for loops and while loops, objects and classes, and mutable variables if you so choose. I feel like the community is trying to shy away from these features for most purposes however, sitcking to the functional core.







However, it does let you do for loops and has an interesting community anddifferent areas of strength.







Maybe more importantly it let's you access a new set of literature and books. Sligthly different but familiar ideas







I think Core is bewildering for a newcomer.







### Rando Trash Poor Style OCaml Snippets







lex_lisp.mll : simplistic usage of ocamllex and menhir






    
    <code>{
      (*
    type token = RightParen | LeftParen | Id of string
    *)
    
    open Lexing
    open Parse_lisp
    
    exception SyntaxError of string
    
    let next_line lexbuf =
      let pos = lexbuf.lex_curr_p in
      lexbuf.lex_curr_p <-
        { pos with pos_bol = lexbuf.lex_curr_pos;
                   pos_lnum = pos.pos_lnum + 1
        }
    }
    
    
    let white = [' ' '\t']+
    let newline = '\r' | '\n' | "\r\n"
    let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
    
    rule read =
      parse
      | white    { read lexbuf }
      | newline  { next_line lexbuf; read lexbuf }
      | '('      { LEFTPAREN }
      | ')'    { RIGHTPAREN }
      | id     {  ID( Lexing.lexeme lexbuf )  }
      | eof     {  EOF }</code>







parse_lisp.mly






    
    <code>%token <string> ID
    %token RIGHTPAREN
    %token LEFTPAREN
    %token EOF
    
    
    
    %start <Ast.tree list> prog
    %%
    
    
    
    prog:
      | s = sexpr; p = prog              { s :: p }
      | EOF                      {[]}
    
    
    sexpr : 
      | LEFTPAREN;  l = idlist; RIGHTPAREN { Ast.Node( l ) }
      | s = ID                         { Ast.Atom(s) } 
    
    (* inefficient because right recursive 
    There are thingy's in menhir to ake this better?
    *)
    idlist :
      | (* empty *) { [] }
      | x = sexpr; l = idlist { x :: l  } 
    
    
    
    (* *)</code>







Doinking around with some graphics






    
    <code>
    open Core
    (* Printf.printf "%b\n" status.keypressed *)
    let loop : Graphics.status -> unit = fun _ -> Graphics.draw_circle 200 200 50;
                                                  Graphics.fill_rect 400 400 50 50
    
    
    
                                                  (* Graphics.synchronize () *)
          
                                        
    
    let main () = Graphics.open_graph ""; 
                  Graphics.set_window_title "My Fun Boy";
                  (* Graphics.auto_synchronize true; *)
                  Graphics.set_color Graphics.black;
                  Graphics.draw_circle 200 200 50;
                  List.iter ~f:(fun i -> Graphics.fill_circle (200 + 20 * i) 200 50) [1;2;3;4];
                  (* Graphics.sound 500 5000; *)
                  let img = Images.load "fish.jpg" [] in 
                  
                  (* Images. *)
                  Images.save "notfish.jpg" (Some Images.Jpeg) [] img;
                  Graphic_image.draw_image img 0 0;
                  Graphics.loop_at_exit [Graphics.Poll;Graphics.Key_pressed] loop
                  (* 
                  let evt = Graphics.wait_next_event [Graphics.Key_pressed] in
                  () *)
    
    
    
    (* let i = create_image 640 640 *)
    (** resize_window  640 640 *)
    
                  
    
    
    let () = main ()</code>







A couple Advent of code 2018






    
    <code>open Core_kernel
    
    (** if I want to try pulling input from the web *)
    (**  https://adventofcode.com/2018/day/1/input *)
    
    let r = In_channel.read_lines "puzz.txt"
    
    
    let main () = Printf.printf "Hey\n";
                  let puzz = In_channel.read_lines "puzz.txt" |>  List.map ~f:int_of_string  in
                  (* List.iter puzz ~f:(fun x -> Printf.printf "%d " x); *)
                  let res = List.fold puzz ~init:0 ~f:(+) in
                  Printf.printf "Sum: %d\n" res
    
    
                 
    let () = main ()</code>






    
    <code>open Core_kernel
    
    (**   
    Obviously the way I'm doing it is not that efficient, nor all that clean really.
    
    *)
    (*
    let exists23 str = let charset = String.to_list str |> Set.of_list (module Char) |> Set.to_list in
                      let counts = List.map ~f:(fun c -> String.count str ~f:(fun y -> y = c)) charset in
                      (List.exists counts ~f:(fun i -> i = 3), List.exists counts ~f:(fun i -> i = 2)) 
    *)
    
    let exists23 str = let charset = String.to_list str |> Set.of_list (module Char) in
                       let counts = Set.map (module Int) ~f:(fun c -> String.count str ~f:((=) c)) charset in
                       (Set.mem counts 2, Set.mem counts 3) 
    
    let main () = Printf.printf "Hey\n";
                  let puzz = In_channel.read_lines "puzz2.txt" in
                  let res = List.map ~f:exists23 puzz in
                  let (c2,c3) = List.fold res ~init:(0,0) ~f:(fun (x,y) (a,b) -> (begin if a then (x + 1) else x end, begin if b then y + 1 else y end)) in
                  Printf.printf "Prod: %d\n" (c2 * c3)
    
    
                 
    let () = main ()</code>







A little Owl usage






    
    <code>open Core_kernel
    open Owl
    
    module Plot = Owl_plplot.Plot
    let () = print_endline "Hello, World!"
    let greeting name = Printf.printf "Hello, %s%i \n%!" name 7
    (* let x : int = 7 *)
    
    let () = greeting "fred"
    (*
    let () = match (In_channel.input_line In_channel.stdin) with
     | None -> ()
     | Some x -> print_endline x
    
    let () = In_channel.with_file "dune" ~f:(fun t -> 
        match In_channel.input_line t with
        | Some x -> print_endline x
        | None -> ()
    )
    *)
    (**
    type 'a mygadt = 
    | Myint : int mygadt
    | Mybool : bool mygadt
     *)
     
    let kmat i j = if i = j then -2.0 
                   else if abs (i - j) = 1 then 1.0 
                   else 0.0
                     
    
    let main () = 
        Mat.print (Mat.vector 10);
        Mat.print (Mat.uniform 5 5);
        Mat.print (Mat.zeros 5 5);
        let h = Owl_plplot.Plot.create "plot_003.png" in
        Plot.set_foreground_color h 0 0 0;
        Plot.set_background_color h 255 255 255;
        Plot.set_title h "Function: f(x) = sine x / x";
        Plot.set_xlabel h "x-axis";
        Plot.set_ylabel h "y-axis";
        Plot.set_font_size h 8.;
        Plot.set_pen_size h 3.;
        (* Plot.plot_fun ~h f 1. 15.; *)
        
        let x = Mat.linspace 0.0 1.0 20 in
        (*let f x = Maths.sin x /. x in
        Plot.plot_fun ~h f 1. 15.; *)
        let y = (Mat.ones 1 20) in
        Mat.print (Mat.ones 1 20);
        Mat.print (Mat.ones 10 1);
        Mat.print y;
        Mat.print x;
        (* y.{0,10} <- 0.0; *)
        (* Mat.set y 10 1 0.0; *)
        Plot.plot ~h x (Mat.vector_ones 20);
        (* Owl_plplot.Plot.plot ~h x (Mat.vector_ones 20); *)
        Owl_plplot.Plot.output h;
        (* let q = Arr.create [|2;2;2|] 1.8 in *)
        let k = Mat.init_2d 10 10 kmat in 
        Mat.print k;
        Linalg.D.inv k |> Mat.print;
        Plot.plot ~h x (Mat.row (Linalg.D.inv k) 5);
        Plot.plot ~h x (Mat.row (Linalg.D.inv k) 7);
        let r = Mat.zeros 1 10 in
        Mat.set r 0 0 (-2.0);
        Mat.set r 0 1 (1.0);
        let k2 = Mat.kron k k in
        let g2 = Linalg.D.inv k2 in
        let s = Mat.row g2 10 in
        let phi = Mat.reshape s [|10;10|] in 
        Plot.plot ~h x (Mat.row  phi 7); (** not convinecd this is actually doing what I want *)
    
        let k' = Mat.toeplitz r in (* also works. more cryptic though *)
        Mat.print k'
    
    
    
    
    
    
    
    let () = main ()</code>



