"""Double-click (or run: python3 start.py) to serve Soul ERP at http://localhost:8000 and open it."""
import http.server, socketserver, webbrowser, os
os.chdir(os.path.dirname(os.path.abspath(__file__)))
PORT = 8000
with socketserver.TCPServer(("127.0.0.1", PORT), http.server.SimpleHTTPRequestHandler) as s:
    webbrowser.open(f"http://localhost:{PORT}/index.html")
    print(f"Soul ERP running at http://localhost:{PORT}  (Ctrl+C to stop)")
    s.serve_forever()
