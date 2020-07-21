from document import Document

doc = Document('thy')
doc.add_line('hello')
doc.add_line('world')

print('before remove_last_line')
doc.print_lines()

doc.remove_last_line()

print('after remove_last_line')
print(doc.get_lines())

# -------------------------------

doc = Document('thy')
doc.add_line('hello')

print('before remove_last_line')
doc.print_lines()

doc.remove_last_line()

print('after remove_last_line')
print(doc.get_lines())

# -------------------------------

doc = Document('thy')
doc.add_line('')

print('before remove_last_line')
doc.print_lines()

doc.remove_last_line()

print('after remove_last_line')
print(doc.get_lines())

# -------------------------------

doc = Document('thy')
doc.add_line('hello')
doc.add_line('world')

print('try to get list of lines')
print(doc.get_lines())