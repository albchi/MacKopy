--- Mackopy.py ---
--- Directory Backup Script ---

import shutil; # copytree
import datetime; datetime
import re; # regular expression
#import sys; # sys.argv[0]

# ask for command line input
while 1:
   cmd = raw_input("Enter a new dir name, or simply hit enter to use default date based dir name :");
   if not(cmd): # user just hit ENTER
      print('ok - you entered nothing - so will use date based dir name');
      break;
   else:
      print ('you entered : ' + cmd );
      ss = len(cmd.split()); # checking the number of words entered 
      if (len(cmd.split())) > 1:  # hopefully only one word
            print ('you entered more than one dir name ' + str(ss) + ', try again ');
      else:
           break;


# get the time
dd = datetime.datetime.now()

# create a string that points to external WD
bb = '/Volumes/My Passport for Mac/';
pp = [
'Desktop/Top',
'Documents/',
'Downloads/',
'Pictures/'
 ];

# combine path and time to create the final path
print('===== Saving ===== ');
for tmp in pp :
   zz = bb+str(dd)+'/'+tmp;

   # print it out

   print('From:');
   print(tmp);
   print('To:');
   print(zz);

   shutil.copytree(tmp, zz);
   print('---------------------------------------');

print('===== End ===== ');

