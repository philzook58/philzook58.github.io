import wx
app = wx.App(False)
frame = wx.Frame(None, title="Demo with Notebook")
nb = wx.Notebook(frame)



nb.AddPage(ExamplePanel(nb), "Absolute Positioning")
nb.AddPage(ExamplePanel(nb), "Page Two")
nb.AddPage(ExamplePanel(nb), "Page Three")
frame.Show()
app.MainLoop()
