/*******************************************************************\

Module: Show the overview for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cmath>
#include <cstdlib>
#include <fstream>

#include <xmllang/xml_parser.h>

#include "../html/html_escape.h"
#include "../html/logo.h"

#include "revisions_report.h"
#include "job_status.h"
#include "deltagit_config.h"
#include "log_scale.h"

const char revisions_report_header[]=
#include "revisions_report_header.inc"
;

/*******************************************************************\

Function: htmlize_message

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string htmlize_message(const std::string &src)
{
  std::string result;
  
  result.reserve(src.size());
  
  for(unsigned i=0; i<src.size(); i++)
    switch(src[i])
    {
    case '<': result+="&lt;"; break;
    case '>': result+="&gt;"; break;
    case '"': result+="&quot;"; break;
    case '\'': result+="&apos;"; break;
    case '&': result+="&amp;"; break;
    case '\n': result+="<br>"; break;
    default:
      if(src[i]>=' ') result+=src[i];
    }
  
  return result;
}

/*******************************************************************\

Function: height

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned height(const job_statust &job_status)
{
  unsigned lines=job_status.added+job_status.deleted;
  if(lines==0) return 0;
  if(lines==1) return 1;
  return log10(lines)*10;
}

/*******************************************************************\

Function: revisions_report

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void revisions_report()
{
  deltagit_configt deltagit_config;
  
  std::string title="DeltaCheck Summary of Revisions";
  if(deltagit_config.description!="")
    title+=" "+deltagit_config.description;
  
  std::list<job_statust> jobs;

  get_jobs(jobs);
  
  unsigned max_height=44; // the hight of log_scale.png
  
  std::ofstream out("index.html");
  
  out << "<html>\n"
         "<head>\n";
        
  out << "<title>" << html_escape(title) << "</title>\n";

  out << revisions_report_header;
  
  out << "</head>\n\n";
  
  out << "<body>\n\n";
  
  out << "<img src=\"" << deltacheck_logo
      << "\" class=\"logo\" alt=\"DeltaCheck Logo\">\n\n";
      
  out << "<div class=\"description\">"
      << html_escape(deltagit_config.description)
      << "</div>\n";

  out << "<div class=\"revisions\">\n";
  
  out << "<table>\n"
      << "<tr><td valign=top>\n"
      << "<img src=\"" << log_scale << "\">\n"
      << "</td>\n<td>\n";
  
  for(std::list<job_statust>::const_iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++)
  {
    // read deltacheck summary, if available
    unsigned passed=0, failed=0;

    {    
      std::string summary_file_name=j_it->id+".wd/deltacheck-stat.xml";
      xmlt deltacheck_summary;
      null_message_handlert null_message_handler;
      parse_xml(summary_file_name, null_message_handler, deltacheck_summary);
      xmlt::elementst::const_iterator deltacheck_stat=deltacheck_summary.find("deltacheck_stat");
      if(deltacheck_stat!=deltacheck_summary.elements.end())
      {
        xmlt::elementst::const_iterator properties=deltacheck_stat->find("properties");
        if(properties!=deltacheck_stat->elements.end())
        {
          passed=atoi(properties->get_attribute("passed").c_str());
          failed=atoi(properties->get_attribute("failed").c_str());
        }
      }
    }
  
    std::string tooltip=
      "<center>"+j_it->id+"</center>"+
      "<font size=2>";
    if(j_it->author!="") tooltip+="Author: "+html_escape(j_it->author)+"<br>";
    if(j_it->date!="") tooltip+="Date: "+html_escape(j_it->date)+"<br>";
    tooltip+=htmlize_message(j_it->message);
    if(j_it->stage!=job_statust::DONE)
    {
      tooltip+="<br><i>"+html_escape(as_string(j_it->stage));
      tooltip+=" "+html_escape(as_string(j_it->status));
      tooltip+="</i>";
    }
    tooltip+=
      "</font>";
      
    unsigned h=std::min(height(*j_it), max_height);

    std::string link;
    std::string bar_color;
    
    if(j_it->stage==job_statust::ANALYSE)
    {
      link=id2string(j_it->id)+".wd/deltacheck-diff.html";
      bar_color="#7070e0";
    }
    else if(j_it->stage==job_statust::DONE)
    {
      link=id2string(j_it->id)+".wd/deltacheck-diff.html";

      unsigned r, g;
      if(passed+failed==0)
      {
        r=0;
        g=255;
      }
      else
      {
        r=(unsigned long long)255*failed/(passed+failed);
        g=(unsigned long long)255*passed/(passed+failed);
      }

      char buffer[100];
      snprintf(buffer, 100, "#%02x%02x30", r, g);
      bar_color=buffer;
    }
    else
    {
      if(j_it->status==job_statust::FAILURE)
        bar_color="#e0e0e0";
      else
        bar_color="#7070e0";
    }
    
    if(link!="")
      out << "<a href=\"" << html_escape(link) << "\">";
    
    out << "<div class=\"revision\""
           " id=\"rev-" << j_it->id << "\""
           " onMouseOver=\"tooltip.show('" << tooltip << "');\""
           " onMouseOut=\"tooltip.hide();\""
           ">";

    out << "<div "
           " style=\"height: " << h << "px;"
           " background-color: " << bar_color << ";"
           " margin-top: " << max_height-h << "px;\""
           ">";

    out << "</div>";
    out << "</div>";
    
    if(link!="")
      out << "</a>";

    out << "\n";
  }
  
  out << "</td></tr></table>\n";
  
  out << "</div>\n";
  
  out << "</body>\n";
  out << "</html>\n";
}
