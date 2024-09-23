import marimo

__generated_with = "0.8.17"
app = marimo.App()


@app.cell
def __():
    x = 4
    return x,


@app.cell
def __():
    1 + 4
    return


@app.cell
def __(mo):
    mo.md("YOLO")
    return


@app.cell
def __(mo):
    mo.md("")
    return


if __name__ == "__main__":
    app.run()
