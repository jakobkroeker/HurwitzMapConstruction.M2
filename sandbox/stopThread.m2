 
taskResult

fktSleep:=()->
(
  sleep 2;
  sleep 2;
  sleep 2;
  sleep 2;
  sleep 2;
)

taskList={}

currTask := createTask(fktSleep);

taskList = taskList | {currTask};


isReady(currTask)

schedule(currTask)
cancelTask(currTask)
isCanceled(currTask)

currTask

while (not isCanceled (currTask)) do {  sleep 1 }; 


isCanceled

isReady(currTask)

cancelTask(currTask)

 for ctask in taskList do ( 
          print ctask;
          if (not isReady(ctask)) then 
            (print "schedule task"; schedule(ctask));  
          print "waiting for task"; 
          -- serialize to check if it works at all
         

          print "task finished";
      );


apply(taskList,elem->print elem);


      tasksFinishedFkt := ()->(return true;);
      tasksFinished := createTask(tasksFinishedFkt);
    --  
    -- for ctask in taskList do
    --   addDependencyTask(tasksFinished,ctask);
    --  print "dependency update ";

      for ctask in taskList do ( 
          print ctask;
          if (not isReady(ctask)) then 
            (print "schedule task"; schedule(ctask));  
          print "waiting for task"; 
          -- serialize to check if it works at all
          while (not isReady (ctask)) do {  sleep 1 }; 
          print "task finished";
      );
      --scheduledTaskList := for task in taskList list  schedule(ctask);
      --for ctask in taskList do ( print ctask; if (not isReady(ctask)) then ( schedule(ctask); print ctask ;));
      --
      --schedule(tasksFinished);
      --apply(scheduledTaskList,elem->print elem);
      print "scheduled";
    
      print "waiting finishing";
      --waiting for finishing:
      for ctask in taskList do ( print ctask;  while (not isReady (ctask)) do {  sleep 1 });
      --while (not isReady (tasksFinished) ) do 
      --{sleep 10;   print "not finished"; sleep 10;};
      print "finished";
      finalRetVal := {};
      print ("#fktEnvelopList= " | #fktEnvelopList);
      for fktEnvelop in fktEnvelopList do
      {
           --print ("#fresults= " | #(fktEnvelop#"resultManager"#"getResults"()));
          mergeResults (resultManager, fktEnvelop#"resultManager");
      };
      return  ;  
