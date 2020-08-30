import requests
import json
from html.parser import HTMLParser
import threading
from queue import Queue
from http_parser.master_parser import MasterParser
from http_parser.general import *


INPUT_FILE = 'HOL-thms.txt'
OUTPUT_DIR = 'HOL Library'
NUMBER_OF_THREADS = 8
queue = Queue()
create_dir(OUTPUT_DIR)
crawl_count = 0


def create_workers():
    for _ in range(NUMBER_OF_THREADS):
        t = threading.Thread(target=work)
        t.daemon = True
        t.start()


def work():
    global crawl_count
    while True:
        url = queue.get()
        crawl_count += 1
        if url.find('/'):
            html = (url.rsplit('/', 1))[1]
            fname = ""
            for car in html:
                fname += car
                if car == '.':
                    break
        MasterParser.parse(url, OUTPUT_DIR, fname)
        queue.task_done()


def create_jobs():
    for url in file_to_set(INPUT_FILE):
        queue.put(url)
    queue.join()

create_workers()
create_jobs()


if __name__ == "__main__":
    pass