import Socket
import Http
import Parser
open Parser

abbrev Request := Http.Request Substring
abbrev Response := Http.Response Substring

-- adapted from https://leanprover-community.github.io/archive/stream/270676-lean4/topic/String.2EcontainsSubstring.html#371017806
def String.isSubstr (pattern : String) (s : String) : Bool :=
  aux 0
where aux (i : String.Pos) :=
  if h : i.byteIdx < s.utf8ByteSize then
    have : s.utf8ByteSize - (s.next i).byteIdx < s.utf8ByteSize - i.byteIdx :=
      Nat.sub_lt_sub_left h (String.lt_next _ _)
    String.substrEq pattern 0 s i pattern.utf8ByteSize
      || aux (s.next i)
  else
    false
termination_by aux i => s.utf8ByteSize - i.byteIdx

-- Receive and parse a request from a connected socket.
-- The given socket should be in the "accepted" state.
def recvRequest (sock : Socket) : IO (Http.Parser.Error ⊕ Request) := do
  let bytes ← Socket.recv sock 4096
  let str := String.fromUTF8Unchecked bytes
  -- Stop parsing when we get to the body of the request.
  -- In other words, leave the request body as an uninterpreted string.
  let stop : Http.Parser Unit := pure ()
  let parsed := Parser.run (Http.Request.parse stop) str
  match parsed with
  | .ok body request => pure (Sum.inr { request with body := body })
  | .error e => pure (Sum.inl e)

def sendResponse (sock : Socket) (response : Response) (htmlContent : String) : IO Unit := do
  let contentTypeHeader := Http.HeaderName.ofHeaderString "Content-Type"
  let updatedHeaders := Http.Headers.add response.headers contentTypeHeader "text/html"
  let responseWithHeaders := { response with headers := updatedHeaders, body := htmlContent }
  let _ ← Socket.send sock responseWithHeaders.toString.toUTF8
  pure ()

def sendBinaryResponse (sock : Socket) (response : Http.Response ByteArray) : IO Unit := do
  let headerStr :=
    s!"{response.version} {response.status.val}" ++
    (response.status.canonicalReason.map (" " ++ ·) |>.getD "") ++
    "\r\n" ++
    response.headers.toRequestFormat ++
    "\r\n\r\n"
  let _ ← Socket.send sock headerStr.toUTF8
  let _ ← Socket.send sock response.body
  pure ()

def servePDF (filePath : System.FilePath) : IO (Option (Http.Response ByteArray)) := do
  if ← filePath.pathExists then
    let content ← IO.FS.readBinFile filePath
    -- Create headers with content type and length using proper HeaderName type
    let headers := Http.Headers.empty
    let contentTypeHeader := Http.HeaderName.ofHeaderString "Content-Type"
    let contentLengthHeader := Http.HeaderName.ofHeaderString "Content-Length"
    let headers := Http.Headers.add headers contentTypeHeader "application/pdf"
    let headers := Http.Headers.add headers contentLengthHeader (toString content.size)
    pure $ some {
      version := Http.Version.HTTP_1_1
      status := Http.StatusCode.OK
      headers := headers
      body := content
    }
  else
    pure none

namespace Response
def ok : Response where
  version := Http.Version.HTTP_1_1
  status := Http.StatusCode.OK
  headers := Http.Headers.empty
  body := ""

def methodNotAllowed : Response where
  version := Http.Version.HTTP_1_1
  status := Http.StatusCode.METHOD_NOT_ALLOWED
  headers := Http.Headers.empty
  body := ""

def notFound : Response where
  version := Http.Version.HTTP_1_1
  status := Http.StatusCode.NOT_FOUND
  headers := Http.Headers.empty
  body := ""
end Response

def normalizePath (path : Http.URI.Path) : Http.URI.Path :=
  -- e.g. the path "/" is parsed to #[""]
  path.filter (λ s => s.length > 0)

-- Add back the ToJson instances
instance : Lean.ToJson Http.Headers where
  toJson headers :=
    headers.toList.map (λ (name, values) =>
      ( name.toHeaderString
      , values.map Lean.Json.str |> List.toArray |> Lean.Json.arr
      )
    )
    |> Lean.Json.mkObj

instance : Lean.ToJson Request where
  toJson req := Lean.Json.mkObj
    [ ("version", Lean.Json.str req.version.toString)
    , ("url", Lean.Json.str req.url.toString)
    , ("method", Lean.Json.str req.method.toString)
    , ("headers", Lean.toJson req.headers)
    , ("body", Lean.Json.str req.body.toString)
    ]

structure Post where
  title: String
  date: String
  author: String
  content: String
  fileName: String

def String.stripQuotes (s: String) : String :=
    if s.startsWith "\"" && s.endsWith "\"" then
      s.drop 1 |>.dropRight 1
    else
      s

def parseFrontMatter (content: String) : Option Post := do
  let lines := content.splitOn "\n"
  if lines.length < 4 then none
  else if lines[0]!.trim != "---" then none
  else
    let endMarker := lines.drop 1 |>.findIdx? (fun l => l.trim == "---")
    match endMarker with
    | none => none
    | some idx =>
      let frontMatter := lines.take (idx + 1) |>.drop 1
      let contentLines := lines.drop (idx + 2)
      let content := String.intercalate "\n" contentLines

      let mut title := ""
      let mut date := ""
      let mut author := ""

      for line in frontMatter do
        let parts := line.splitOn ":"
        if parts.length >= 2 then
          let key := parts[0]!.trim.toLower
          let value := parts[1]!.trim.stripQuotes
          match key with
          | "title" => title := value
          | "date" => date := value
          | "author" => author := value
          | _ => pure ()

      some { title := title, date := date, author := author, content := content, fileName := "" }

def loadPosts (dir: System.FilePath) : IO (List Post) := do
  let poastsDir := dir / "poasts"
  let entries ← poastsDir.readDir
  let mut posts := []
  for entry in entries do
    if entry.fileName.endsWith ".md" then
      let content ← IO.FS.readFile (poastsDir / entry.fileName)
      match parseFrontMatter content with
      | some post =>
        let post := {post with fileName := entry.fileName.dropRight 3}
        posts := posts ++ [post]
      | none => continue
  return posts.reverse

def String.splitReturnDelimitersAux (s : String) (p : Char → Bool) (b : Pos) (i : Pos) (r : List String) : List String :=
  if h : s.atEnd i then
    let r := (s.extract b i)::r
    r.reverse
  else
    have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (lt_next s _)
    if p (s.get i) then
      let i' := s.next i
      splitReturnDelimitersAux s p i' i' ((s.get i).toString :: (s.extract b i) :: r)
    else
      splitReturnDelimitersAux s p b (s.next i) r
termination_by _ => s.endPos.1 - i.1

def String.splitReturnDelimiters (s : String) (p : Char → Bool) : List String :=
  splitReturnDelimitersAux s p 0 0 []

def processLinks (line: String) : String :=
  -- Simple approach: look for pattern [text](url)
  let parts := line.splitOn "["

  parts.enum.foldl (fun acc (i, part) =>
    if i == 0 then
      acc ++ part
    else
      -- part starts after a '[', look for ']('
      match part.splitOn "](" with
      | linkText :: rest =>
        if rest.length > 0 then
          -- Found '](' pattern
          let remaining := String.intercalate "](" rest
          match remaining.splitOn ")" with
          | url :: afterLink =>
            if afterLink.length > 0 then
              -- Found complete link pattern
              acc ++ s!"<a href=\"{url}\">{linkText}</a>" ++ String.intercalate ")" afterLink
            else
              -- No closing ')'
              acc ++ "[" ++ part
          | [] => acc ++ "[" ++ part
        else
          -- No '](' found
          acc ++ "[" ++ part
      | [] => acc ++ "[" ++ part
  ) ""

def processMarkdown (content: String) : String := Id.run do
  let lines := content.splitOn "\n"
  let mut processed := ""
  let mut inCodeBlock := false
  let mut language := ""

  for line in lines do
    if line.startsWith "```" then
      if inCodeBlock then
        processed := processed ++ "</code></pre>"
        inCodeBlock := false
      else
        language := line.drop 3
        processed := processed ++ s!"<pre><code class=\"language-{language}\">"
        inCodeBlock := true
    else if inCodeBlock then
      processed := processed ++ line ++ "\n"
    else if line.startsWith "<a" then
      processed := processed ++ line ++ "<br>"
    else
      processed := processed ++ processLinks line ++ "<br>"
  processed

def createSubstackHeader : String :=
  "<div class=\"substack-header\"><a href=\"https://substack.com/@typeofemale\">📖 Read and subscribe to my Substack newsletters, Algorithmically Gavaged Intelligence and Antediluvian Garrulous Autodidatic Midshit Polymath for my musings, I will use this blog for more technical stuff!!</a></div>"

def generateHTML (post : Post) (cssContent: String) : String :=
  "<html>" ++
  "<head><meta charset='UTF-8'>" ++
    "<title>" ++ post.title ++ "</title>" ++
    "<style>" ++ cssContent ++ "</style>" ++
    "<link rel=\"stylesheet\" href=\"https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/styles/default.min.css\">" ++
    "<script src=\"https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/highlight.min.js\"></script>" ++
    "<script src=\"https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/languages/rust.min.js\"></script>" ++
    "<script src=\"https://unpkg.com/highlightjs-lean/dist/lean.min.js\"></script>" ++
    "<script>hljs.highlightAll();</script>" ++
  "</head>" ++
  "<body class=\"trans-theme\">" ++
    createSubstackHeader ++
    "<h1>" ++ post.title ++ "</h1>" ++
    "<p>By " ++ post.author ++ " on " ++ post.date ++ "</p>" ++
    "<div class='content'>" ++ processMarkdown post.content ++ "</div>" ++
  "</body>" ++
"</html>"

def generateIndex (posts: List Post) (cssContent: String) : String :=
  let links := posts.map (λ post =>
    s!"<li><a href=\"/{post.fileName}\">{post.date} - {post.title}</a></li>")
  let linksList := String.intercalate "\n" links
  "<html><meta charset='UTF-8'><head><style>" ++ cssContent ++ "</style><title>typeo's musings (lean edition)</title></head><body class=\"trans-theme\">" ++
  createSubstackHeader ++
  "<h1>Braindump: </h1>" ++
  s!"<ul>{linksList}</ul>" ++
  "</body></html>"

def main : IO Unit := do
  let sock ← Socket.mk Socket.AddressFamily.inet Socket.Typ.stream
  Socket.bind sock (Socket.SockAddr4.v4 (Socket.IPv4Addr.mk 0 0 0 0) 3000)
  Socket.listen sock 32

  let posts ← loadPosts (System.FilePath.mk ".")
  let cssContent ← IO.FS.readFile "trans.css"
  try repeat do
    let (sock', _) ← Socket.accept sock
    let request ← match (← recvRequest sock') with
      | .inr request => pure request
      | .inl e => do
        IO.println s!"Could not parse request: {e}"
        continue

    IO.println (request |> Lean.toJson |> Lean.Json.compress)
    let path := normalizePath request.url.path

    match request.method, path with
    | .GET, #[] =>
      let htmlContent := generateIndex posts cssContent
      sendResponse sock' Response.ok htmlContent
    | .GET, #[pageName] =>
      if pageName.endsWith ".pdf" then
        match (← servePDF (System.FilePath.mk s!"./pdfs/{pageName}")) with
        | some response =>
          sendBinaryResponse sock' response
        | none =>
          let htmlContent := "<html><body class=\"trans-theme\"><h1>PDF Not Found</h1></body></html>"
          sendResponse sock' Response.notFound htmlContent
      else
        match posts.find? (λ post => post.fileName == pageName) with
        | some post =>
          let htmlContent := generateHTML post cssContent
          sendResponse sock' Response.ok htmlContent
        | none =>
          let htmlContent := "<html><body class=\"trans-theme\"><h1>Page Not Found</h1></body></html>"
          sendResponse sock' Response.notFound htmlContent
    | .GET, _ =>
      let htmlContent := "<html><body class=\"trans-theme\"><h1>Page Not Found</h1></body></html>"
      sendResponse sock' Response.notFound htmlContent
    | _, _ =>
      sendResponse sock' Response.methodNotAllowed ""
    Socket.close sock'
  finally do
    Socket.close sock
