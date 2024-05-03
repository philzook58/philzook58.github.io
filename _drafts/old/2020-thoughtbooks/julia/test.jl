function foo()
    println("fodsfgdfsdffdso")
end

foo()

using BenchmarkTime
for i in 1:10
    i * 20
end

using Plots
x = 1:10; y = rand(10); # These are the plotting data 
plot(x,y, label="my label")