%% Comment
-module(markov-chain).
-exports(sum/1).

sum(List) ->
     sum(List, 0).

sum([],Sum) ->
    Sum;
sum([Head | Rest], Sum) ->
    sum(Rest. Sum + Head).
% my_list:sum is how to call module

%unused had variable
some_function(_Head, []) ->
    [].

tokenize(Text)->
    string:tokens(Text, " \t\n").


