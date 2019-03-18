-module(drinks).
-export([machine/2]).

machine(null, null) ->
  receive
    {select, [I1]} ->
      machine(I1, 0)
  end;
machine(R1, R2) when R2 >= 100 ->
  receive
    {coin, [I1]} ->
      io:format("~p~n", [R2+I1]),
      machine(R1, R2+I1);
    {vend, []} ->
      io:format("~p~n", [R1]) % This line doesn't give change
      % io:format("~p~n", [R1, R2 - 100]) % This line does give change

      % , machine(R1, R2) % This line produces the bug such that you can get infinite drinks out once you've paid
      % , machine(null, null) % This line does resets the machine
      % , machine(null, R2 - 100) % This allows money to be carried forward
  end;
machine(R1, R2) when R2 < 100 ->
  receive
    {coin, [I1]} ->
      io:format("~p~n", [R2+I1]),
      machine(R1, R2+I1);
    {vend, []} ->
      machine(R1, R2)
  end.
