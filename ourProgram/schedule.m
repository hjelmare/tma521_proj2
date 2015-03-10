clear all
clc
clf

xShift = 0.2;
yShift = xShift;

sched = load('final_x_15jobs.txt');
proc = load('15jobs_procTime.txt');
outFile = 'schedule15.png';

nJobs = length(sched);

cc = jet(nJobs);

for i = 1:nJobs
    plotParam = [sched(i,3), sched(i,2)-0.5, proc(i,2),1 ];
    rectangle('Position',plotParam,'FaceColor',cc(i,:))
    text(plotParam(1)+xShift, plotParam(2)+yShift, num2str(i))
end

axis([0,45,0,6])    % 15 jobs
%axis([0,95,0,6])    % 30 jobs

xlabel('Timestep','FontSize',14)
ylabel('Machine nr','FontSize',14)

saveas(gcf,outFile,'png');
