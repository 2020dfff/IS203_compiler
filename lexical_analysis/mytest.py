import os

test_samples_path = "sealpps"
out_path = "mytest_results"
test_samples = os.listdir(test_samples_path)
os.system("rm -rf ./mytest_results/*")
for i, test_sample in enumerate(test_samples):
    test_sample2 = os.path.join(test_samples_path, test_sample)
    out_sample = os.path.join(out_path, test_sample.split(".")[0]+".out")
    sen = "./test < {} > {}".format(test_sample2, out_sample)
    os.system(sen)
    print(sen)
    print(test_sample,"ok!")
