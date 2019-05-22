import BaseHTTPServer
import subprocess
import sys

MUNTA_PATH = "./munta"
PORT = 3069


def run_munta(query):
    p = subprocess.Popen([MUNTA_PATH, '-s'],
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    return p.communicate(input=query)


class handler(BaseHTTPServer.BaseHTTPRequestHandler):
    def _set_headers(self):
        self.send_response(200)
        self.send_header('Content-type', 'text/html')
        self.send_header('Access-Control-Allow-Origin', '*')
        self.end_headers()

    def do_GET(self):
        self._set_headers()
        self.wfile.write("<html><body>GET is not supported</body></html>")

    def do_POST(self):
        content_length = int(self.headers['Content-Length'])
        post_data = self.rfile.read(content_length)
        self._set_headers()
        self.wfile.write(run_munta(post_data)[0])


def run(server_class=BaseHTTPServer.HTTPServer, handler_class=handler):
    server_address = ('', PORT)
    httpd = server_class(server_address, handler_class)
    httpd.serve_forever()


if __name__ == "__main__":
    print("Server started.")
    try:
        run()
    except KeyboardInterrupt:
        print("Server shutting down.")
        sys.exit(0)
