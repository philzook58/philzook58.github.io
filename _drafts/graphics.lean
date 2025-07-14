
-- https://unnamed.website/posts/bad-apple-lean-tactic/ They parse ppm


-- PPM writing

#eval do
  IO.FS.writeFile "/tmp/test.ppm" r#"P3
# "P3" means this is a RGB color image in ASCII
# "3 2" is the width and height of the image in pixels
# "255" is the maximum value for each color
# This, up through the "255" line below are the header.
# Everything after that is the image data: RGB triplets.
# In order: red, green, blue, yellow, white, and black.
3 2
255
255   0   0
  0 255   0
  0   0 255
255 255   0
255 255 255
  0   0   0
"#

def bash (code : String) (_ : Unit) : IO Unit := do
  let out <- IO.Process.output {
    cmd := "bash",
    args := #["-c", code],
  }
  IO.println out.stdout
  IO.println out.stderr


#eval bash "LD_LIBRARY_PATH=/lib eog /tmp/test.ppm"
