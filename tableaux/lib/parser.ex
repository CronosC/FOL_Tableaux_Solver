defmodule Parser do
  @moduledoc """
  leex and yecc based parser for the TPTP language.
  """
  def lex(str) do
    :TPTP_lexer.string(to_charlist(str))
  end

  def parse_tokens(tokens) do
    :TPTP_parser.parse(tokens)
  end

  def parse(str) do
    :TPTP_parser.parse(:TPTP_lexer.string(to_charlist(str)))
  end

  def parse_TPTP_from_str(str) do
    {errorcode_lex, tokens, _} = :TPTP_lexer.string(to_charlist(str))
    case errorcode_lex do
      :ok ->
        {errorcode_parse, expression} = :TPTP_parser.parse(tokens)
        case errorcode_parse do
          :ok ->
            #IO.puts("Parsing successful!")
            expression
          _ ->
            IO.puts("Error parsing tokens!")
            :error_parsing
        end
      _ ->
        IO.puts("Error lexing string!")
        :error_lexing
    end
  end

  def parse_TPTP_from_file(path) do
    {errorcode_read, file_str} = File.read(path)
    case errorcode_read do
      :ok -> parse_TPTP_from_str(file_str)
      _ ->
        IO.puts("Error reading file!")
        :error_read_file
    end
  end
end
