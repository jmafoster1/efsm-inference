defmodule Test do
  def applyOp(a, b, op) do
    op.(a, b)
  end
end

IO.inspect Test.applyOp(1, 2, fn(x, y) -> x > y end)
