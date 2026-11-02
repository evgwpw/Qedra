param(
    [int]$Port = 8080,
    [switch]$NoBrowser
)
# WASM.2d: minimal static server for web\dist\wwwroot on the built-in .NET stack (no extra software).
# TCP listener + one request per connection (Connection: close): HttpListener подвешивал страницу
# на повторных запросах к крупным файлам, здесь цикл простой и предсказуемый.
$ErrorActionPreference = 'Stop'
$root = Join-Path $PSScriptRoot 'dist\wwwroot'
if (-not (Test-Path $root)) {
    Write-Host "web\dist not found - run build.cmd first"
    exit 1
}
$rootFull = (Resolve-Path $root).Path
$rootPrefix = $rootFull.TrimEnd('\') + '\'

$mime = @{
    '.html' = 'text/html; charset=utf-8'
    '.js'   = 'text/javascript; charset=utf-8'
    '.mjs'  = 'text/javascript; charset=utf-8'
    '.css'  = 'text/css; charset=utf-8'
    '.json' = 'application/json; charset=utf-8'
    '.wasm' = 'application/wasm'
    '.dat'  = 'application/octet-stream'
    '.woff2' = 'font/woff2'
    '.wav'  = 'audio/wav'
    '.svg'  = 'image/svg+xml'
    '.png'  = 'image/png'
    '.ico'  = 'image/x-icon'
    '.txt'  = 'text/plain; charset=utf-8'
}

$listener = [System.Net.Sockets.TcpListener]::new([System.Net.IPAddress]::Loopback, $Port)
$listener.Start()
$url = "http://localhost:$Port/app/index.html"
Write-Host "Serving $rootFull on port $Port"
Write-Host "Open $url"
if (-not $NoBrowser) { Start-Process $url }

function Send-Bytes($stream, [byte[]]$bytes) {
    $stream.Write($bytes, 0, $bytes.Length)
}

while ($true) {
    $client = $listener.AcceptTcpClient()
    try {
        $client.ReceiveTimeout = 5000
        $client.SendTimeout = 30000
        $stream = $client.GetStream()

        # читаем заголовки до пустой строки
        $buf = New-Object byte[] 8192
        $text = ''
        while ($text.IndexOf("`r`n`r`n") -lt 0 -and $text.Length -lt 65536) {
            $n = $stream.Read($buf, 0, $buf.Length)
            if ($n -le 0) { break }
            $text += [System.Text.Encoding]::ASCII.GetString($buf, 0, $n)
        }
        $line = ($text -split "`r`n")[0]
        $parts = $line -split ' '
        if ($parts.Length -lt 2) { continue }
        $path = [System.Uri]::UnescapeDataString($parts[1].Split('?')[0])
        if ($path -eq '/') { $path = '/app/index.html' }

        $rel = $path.TrimStart('/') -replace '/', '\'
        $full = [System.IO.Path]::GetFullPath((Join-Path $rootFull $rel))
        $status = '200 OK'
        $body = $null
        $type = 'application/octet-stream'
        if (-not $full.StartsWith($rootPrefix) -or -not (Test-Path $full -PathType Leaf)) {
            $status = '404 Not Found'
            $body = [System.Text.Encoding]::UTF8.GetBytes('404 ' + $path)
            $type = 'text/plain; charset=utf-8'
        }
        else {
            $ext = [System.IO.Path]::GetExtension($full).ToLowerInvariant()
            if ($mime.ContainsKey($ext)) { $type = $mime[$ext] }
            $body = [System.IO.File]::ReadAllBytes($full)
        }

        $head = "HTTP/1.1 $status`r`nContent-Type: $type`r`nContent-Length: $($body.Length)`r`n" +
                "Cache-Control: no-cache`r`nConnection: close`r`n`r`n"
        Send-Bytes $stream ([System.Text.Encoding]::ASCII.GetBytes($head))
        Send-Bytes $stream $body
        $stream.Flush()
    }
    catch {
        # обрыв соединения или таймаут чтения — просто идём к следующему
    }
    finally {
        try { $client.Close() } catch { }
    }
}
