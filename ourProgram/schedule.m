clear all
clc
clf


nSteps = 30;
nJobs = 15;
nMach = 5;

UBD = dlmread('outRestricted.txt',' ');
pi = dlmread('outPi.txt',' ');
gamma = dlmread('outGamma.txt',' ');
colSub = dlmread('outColumnSub.txt',' ');

pi = reshape(pi,nSteps,nJobs);
gamma = reshape(gamma, nSteps, nMach);
colSub = reshape(colSub, nSteps, nMach);

%bar(gamma)
%
LBD = zeros(1,nSteps);
for iStep = 1:nSteps
    LBD(iStep) = sum(pi(iStep,:)) + sum(gamma(iStep,:));
end

hold on
plot(UBD,'bo-')
plot(LBD,'r.-')
hold off