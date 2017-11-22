defmodule Guard do
  def compatible([], _) do
    true
  end
  def compatible(_, []) do
    true
  end
  def compatible([h1|t1], [h2|t2]) do
    true
  end
end
