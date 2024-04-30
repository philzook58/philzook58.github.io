using PkgTemplates

t = Template(; 
    user="philzook58",
    dir="~/Documents/python/thoughtbooks/julia/",
    authors="Philip Zucer",
    julia=v"1.5",
    plugins=[
        License(; name="MIT"),
        Git(; manifest=true, ssh=true),
        GitHubActions(; x86=true),
        Codecov(),
        Documenter{GitHubActions}(),
        Develop(),
    ],
)
t("MyPkg")