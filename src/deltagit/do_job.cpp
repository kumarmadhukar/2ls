/*******************************************************************\

Module: Do a jobs for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <unistd.h>

#include <cstdlib>
#include <cassert>
#include <iostream>
#include <fstream>

#include <util/prefix.h>
#include <util/tempfile.h>

#include "job_status.h"
#include "do_job.h"

/*******************************************************************\

Function: check_out

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void check_out(job_statust &job_status)
{
  const std::string working_dir=job_status.get_wd();
  
  // check if we already have it
  if(access((working_dir+"/.git/HEAD").c_str(), R_OK)==0)
  {
    std::cout << "git repository for " << job_status.id
              << " already present\n";
    job_status.next_stage();
    job_status.write();  
    return;
  }

  std::cout << "Checking out " << job_status.id << "\n";

  job_status.status=job_statust::RUNNING;
  job_status.set_hostname();
  job_status.write();

  std::string command;

  // Do a shared clone -- this uses very little disc space.
  // Will overwrite checkout log.
  command="git clone --no-checkout --shared source-repo "+
          working_dir+
          " > jobs/"+job_status.id+".checkout.log 2>&1";

  int result1=system(command.c_str());
  if(result1!=0)
  {
    job_status.status=job_statust::FAILURE;
    job_status.write();
    return;
  }
  
  // Now do checkout; this will eat disc space.
  command="(cd "+working_dir+"; "+
          "git checkout --detach "+job_status.commit+
          ") >> jobs/"+job_status.id+".checkout.log 2>&1";

  int result2=system(command.c_str());

  if(result2!=0)
  {
    job_status.status=job_statust::FAILURE;
    job_status.write();
    return;
  }

  job_status.next_stage();
  job_status.write();  
}

/*******************************************************************\

Function: build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void build(job_statust &job_status)
{
  std::cout << "Building " << job_status.id << "\n";

  const std::string working_dir=job_status.get_wd();
  
  job_status.status=job_statust::RUNNING;
  job_status.set_hostname();
  job_status.write();

  std::string command;

  // Now run build script in working directory.
  command="(cd "+working_dir+"; ../../build"+
          ") >> jobs/"+job_status.id+".build.log 2>&1";

  int result=system(command.c_str());
  
  if(result!=0)
  {
    job_status.status=job_statust::FAILURE;
    job_status.write();
    std::cout << "Build has failed\n";
    return;
  }

  std::cout << "Build successful\n";

  job_status.next_stage();
  job_status.write();  
}

/*******************************************************************\

Function: analyse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void analyse(
  job_statust &job_status,
  const std::list<job_statust> &jobs)
{
  // get the job before this one

  std::string previous="";

  for(std::list<job_statust>::const_iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++)
  {
    if(j_it->id==job_status.id) break;
    previous=j_it->id;
  }
  
  if(previous!="")
  {
    std::cout << "Differential analysis between "
              << previous << " and " << job_status.id
              << "\n";

    // is it built already?
    job_statust old_version(previous);

    if(old_version.stage!=job_statust::ANALYSE &&
       old_version.stage!=job_statust::DONE)
    {
      std::cout << "Job " << previous << " is not built yet\n";
      return;
    }
    
    job_status.status=job_statust::RUNNING;
    job_status.set_hostname();
    job_status.write();
    
    std::string command=
      "./analyse \""+previous+"\" \""+job_status.id+"\""
      " > jobs/"+job_status.id+".analysis.log 2>&1";

    int result=system(command.c_str());
    
    if(result!=0)
    {
      job_status.status=job_statust::FAILURE;
      job_status.write();
      std::cout << "Analysis has failed\n";
      return;
    }

    job_status.next_stage();
    job_status.write();    
    std::cout << "Analysis completed\n";
  }
  else
  {
    std::cout << "One-version analysis for " << job_status.id
              << "\n";

    job_status.status=job_statust::RUNNING;
    job_status.set_hostname();
    job_status.write();
    
    std::string command=
      "./analyse-one \""+job_status.id+"\""
      " > jobs/"+job_status.id+".analysis.log 2>&1";

    int result=system(command.c_str());
    
    if(result!=0)
    {
      job_status.status=job_statust::FAILURE;
      job_status.write();
      std::cout << "Analysis has failed\n";
      return;
    }

    job_status.next_stage();
    job_status.write();    
    std::cout << "Analysis completed\n";
  }
}

/*******************************************************************\

Function: do_job

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void do_job(job_statust &job_status,
            const std::list<job_statust> &jobs)
{
  if(job_status.status==job_statust::FAILURE)
  {
    std::cout << "Job " << job_status.id << " has failed, "
                 "consider resetting it.\n";
  }
  else if(job_status.status==job_statust::RUNNING)
  {
    std::cout << "Job " << job_status.id
              << " is already running.\n";
  }
  else if(job_status.status==job_statust::COMPLETED)
  {
    std::cout << "Job " << job_status.id
              << " is already completed.\n";
  }
  else
  {
    switch(job_status.stage)
    {
    case job_statust::INIT: return; // done by deltagit init
    case job_statust::CHECK_OUT: check_out(job_status); break;
    case job_statust::BUILD: build(job_status); break;
    case job_statust::ANALYSE: analyse(job_status, jobs); break;
    case job_statust::DONE: break;
    }
  }

}

/*******************************************************************\

Function: do_job

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void do_job(const std::string &id)
{
  // get job list
  std::list<job_statust> jobs;
  get_jobs(jobs);

  // get current job status
  job_statust job_status(id);
  do_job(job_status, jobs);
}

/*******************************************************************\

Function: do_job

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void do_job()
{
  // get job list
  std::list<job_statust> jobs;
  get_jobs(jobs);
  
  // Do a job that needs work,
  // starting from the end of the log.
  for(std::list<job_statust>::reverse_iterator
      j_it=jobs.rbegin();
      j_it!=jobs.rend();
      j_it++)
  {
    if(j_it->stage!=job_statust::DONE &&
       j_it->stage!=job_statust::INIT &&
       j_it->status==job_statust::WAITING)
    {
      std::cout << "Doing job " << j_it->id << std::endl;
      do_job(*j_it, jobs);
      return;
    }
  }
}

