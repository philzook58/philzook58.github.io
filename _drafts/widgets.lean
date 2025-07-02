import ProofWidgets.Component.HtmlDisplay
import Lean.Widget.Types
import ProofWidgets.Data.Svg
open scoped ProofWidgets.Jsx
open ProofWidgets Svg

#eval "hello"

-- click on the line below to see it in your infoview!
#html <b>You can use HTML in Lean {.text s!"{1 + 3}"}!</b>


-- raw
-- https://lean-lang.org/lean4/doc/examples/widgets.lean.html
@[widget_module]
def helloWidget : Lean.Widget.Module where
  javascript := "
    import * as React from 'react';
    export default function(props) {
      const name = props.name || 'world'
      return React.createElement('p', {}, 'Hello ' + name + '!')
    }"
#widget helloWidget


private def frame : Frame where
  xmin   := 0
  ymin   := 0
  xSize  := 450
  width  := 450
  height := 450
private def github : Svg frame :=
  { elements := #[
    rect (100.0, 100.0) (.abs 70.0) (.abs 70.0)
        |>.setStroke (255., 0., 0.) (.px 2)
        |>.setFill (0.5, 0.5, 0.5),] }
#html github.toHtml
