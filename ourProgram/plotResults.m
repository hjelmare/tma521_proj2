% Plot reduced cost, UBD and LBD
clear all
clc

data = dlmread('iterationResult.txt',' ');
iIteration = data(:,1);
reducedCost = data(:,2);
UBD = data(:,3);
LBD = data(:,4);

hold on
plot(iIteration, UBD, 'b')
plot(iIteration, LBD, 'r')
legend('UBD', 'LBD')
xlabel('iteration number', 'FontSize', 14)

figure
plot(iIteration, reducedCost)
legend('Reduced cost')
xlabel('iteration number', 'FontSize', 14)