import os

class Document:
    # theorems = [] # list of theorems
    # theorem_dict = {} # maps theorems to position in the document.
    # thy_file = None # FileEditor of the document

    def __init__(self, filename, prefix = '', suffix = '.thy', GYM_DIR = '.'):
        self.prefix = prefix
        self.filename = filename
        self.suffix = suffix
        self.dir = GYM_DIR + '/tmp'
        if not os.path.exists(self.dir):
            try:
                os.makedirs(self.dir)
            except OSError as e:
                print('[ERROR] error while creating temp directory. \n')
                raise
        
        # prepare to overwrite old file
        self.file = open(self.dir + "/" + prefix + filename + suffix, "w")
        self.file.write('')
        self.file.close()

        self.name_without_suffix = self.file.name[:-len(suffix)]

    def add_line(self, line):
        self.file = open(self.dir + "/" + self.prefix + self.filename + self.suffix, "a")
        self.file.write(line + '\n')
        self.file.close()

    def add_lines(self, lines):
        for each in lines:
            add_line(each)

    def remove_last_line(self):
        with open(self.dir + "/" + self.prefix + self.filename + self.suffix, "r+", encoding = "utf-8") as file:
            file.seek(0, os.SEEK_END)
            pos = file.tell() - 1
            while pos > 0 and file.read(1) != "\n":
                pos -= 1
                file.seek(pos, os.SEEK_SET)
            if pos > 0:
                file.seek(pos + 1, os.SEEK_SET)
                file.truncate()
    
    def get_lines(self, decode = False):
        self.file = open(self.dir + "/" + self.prefix + self.filename + self.suffix, "r")
        new_list = []
        self.file.seek(0)
        for each in self.file.readlines():
            if (decode):
                new_list.append(each.decode('utf-8').strip())
            else:
                new_list.append(each)
        return new_list

    def print_lines(self, decode = False):
        self.file = open(self.dir + "/" + self.prefix + self.filename + self.suffix, "r")
        self.file.seek(0)
        for each in self.get_lines(decode):
            print(each, end =" ")

    def get_name(self):
        return self.name_without_suffix

    def add_theorem(self, theorem_lines):
        add_lines(theorem_lines) # dah..

    def close(self):
        self.file.close()
        
    def open(self):
        self.file = open(self.dir + "/" + self.prefix + self.filename + self.suffix, "r")



