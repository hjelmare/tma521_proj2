% Plot reduced cost, UBD and LBD
clear all
clc
close all

data = dlmread('iterationResult_30jobs.txt',' ');
iIteration = data(:,1);
CPU = data(:,2);
reducedCost = data(:,3);
UBD = data(:,4);
LBD = data(:,5);

%figure
a = axes('units', 'normalized','position',[.1 .25 .8 .7], 'xlim',[0 iIteration(end)], 'xtick', 0:10:iIteration(end));
xlabel(a, 'Iteration number', 'FontSize', 14);
hold on
plot(iIteration, UBD, 'b')
plot(iIteration, LBD, 'r')
legend('UBD', 'LBD')
b=axes('units','normalized','position',[.1 .1 .8 0.000001],'xlim',[0 CPU(end)],'color','none');
xlabel(b,'CPU time', 'FontSize', 14)


figure
a = axes('units', 'normalized','position',[.1 .25 .8 .7], 'xlim',[0 iIteration(end)], 'xtick', 0:10:iIteration(end));
xlabel(a, 'Iteration number', 'FontSize', 14);
plot(iIteration, reducedCost)
legend('Reduced cost')
b=axes('units','normalized','position',[.1 .1 .8 0.000001],'xlim',[0 CPU(end)],'color','none');
xlabel(b,'CPU time', 'FontSize', 14)