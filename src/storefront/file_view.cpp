/*******************************************************************\

Module: Trace View

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>
#include <fstream>

#include "../html/html_escape.h"
#include "../html/syntax_highlighting.h"

#include "data.h"

/*******************************************************************\

Function: file_view

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void print_file(const datat &data, irep_idt file, std::ostream &out)
{
  out << "<div class=\"file\">\n";
  out << "<div class=\"filename\">" << html_escape(file) << "</div>\n";
  out << "<div class=\"listing\">\n";

  std::ifstream in(file.c_str());
  if(!in)
  {
  }
  else
  {
    // line to entry number
    std::map<unsigned, std::vector<unsigned> > line_map;
    
    for(datat::entriest::const_iterator
        e_it=data.entries.begin();
        e_it!=data.entries.end();
        e_it++)
      if(e_it->file==file)
      {
        line_map[e_it->line].push_back(e_it-data.entries.begin());
      }
  
    syntax_highlightingt syntax_highlighting(out);

    unsigned line_no=1;

    std::string line;
    while(std::getline(in, line))
    {
      syntax_highlighting.strong_class="";
      syntax_highlighting.line_no=line_no;
      
      std::vector<unsigned> &entries=line_map[line_no];
      
      if(!entries.empty())
      {
        syntax_highlighting.strong_class="alarm";
      }
      
      syntax_highlighting(line);
      
      line_no++;
    }
  }
  
  out << "</div></div>\n\n";
}

/*******************************************************************\

Function: file_view

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void file_view(const datat &data)
{
  std::ofstream out("file_view.html");

  out << "<html>\n<head>\n";
  out << "<title>" << html_escape(data.description) << "</title>\n";
  
  out << "<style type=\"text/css\">\n";
  out << "/* Source-code listing */\n";
  out << "div.file { float: left; padding-right: 20px; }\n";
  out << "div.listing { font-size: 6px; width: 150px; overflow: scroll; }\n";
  out << "div.filename { text-align: center; font-size: 12px; width: 150px; }\n";

  out << "strong.alarm { font-style: normal; background-color: #ff6633; font-weight: normal; }\n";
  
  out << "/* Description of sw under test */\n";
  out << "div.description { float: center; font: 14px \"Trebuchet MS\", Verdana, Arial, Helvetica, sans-serif;  width=100%; text-align: center; }\n";
  
  out << "</style>\n";
  out << "</head>\n";
  
  out << "<body>\n";
  
  out << "<center><img src=\"http://www.deltacheck.org/deltacheck_logo_small.png\"></center>\n";
  
  out << "<div class=\"description\">\n";
  out << html_escape(data.description) << "\n";
  out << "</div>\n";
  
  std::set<irep_idt> files;
  
  for(datat::entriest::const_iterator
      e_it=data.entries.begin();
      e_it!=data.entries.end();
      e_it++)
    files.insert(e_it->file);

  for(std::set<irep_idt>::const_iterator
      f_it=files.begin();
      f_it!=files.end();
      f_it++)
  {
    print_file(data, *f_it, out);
  }
  
  out << "</body>\n</html>\n";
}