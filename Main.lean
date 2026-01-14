import LParse

def main : IO Unit :=
  IO.println s!"Hello, {parse (many (char 's')) "s".toList}!"
