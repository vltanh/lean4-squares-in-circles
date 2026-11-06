# Complete case tree

Node N00000 is the root. A bound context is applied first; its simultaneous updates and outward beta-to-w conversion determine the state for the action. The children listed for an angle or center split include the common endpoint. No branch is discarded.

| Node | Bound context | Action | Children or terminal context |
|---|---|---|---|
| N00000 | C00000 | vertical(1,5) | N00001, N04230 |
| N00001 | C00001 | assumed CD primary | N00002 |
| N00002 | none | CD angle sign | N00003 |
| N00003 | C00002 | angle(7,0) | N00004, N02387 |
| N00004 | C00003 | angle(8,0) | N00005, N01606 |
| N00005 | C00004 | angle(6,0) | N00006, N00595 |
| N00006 | C00005 | angle(5,0) | N00007, N00282 |
| N00007 | C00006 | angle(4,0) | N00008, N00135 |
| N00008 | C00007 | angle(3,-13573/65536) | N00009, N00010 |
| N00009 | C00008 | positive row contradiction | C00009 |
| N00010 | C00010 | proxy(1,8) | N00011, N00012, N00077, N00094 |
| N00011 | none | positive row contradiction | C00011 |
| N00012 | C00012 | proxy(5,8) | N00013, N00014, N00023, N00074 |
| N00013 | none | positive row contradiction | C00013 |
| N00014 | C00014 | proxy(2,8) | N00015, N00016, N00017, N00018 |
| N00015 | none | positive row contradiction | C00015 |
| N00016 | C00016 | positive row contradiction | C00017 |
| N00017 | none | positive row contradiction | C00018 |
| N00018 | C00019 | proxy(3,8) | N00019, N00020, N00021, N00022 |
| N00019 | none | positive row contradiction | C00020 |
| N00020 | none | positive row contradiction | C00021 |
| N00021 | none | positive row contradiction | C00022 |
| N00022 | C00023 | positive row contradiction | C00024 |
| N00023 | C00025 | angle(6,-13539/65536) | N00024, N00025 |
| N00024 | none | positive row contradiction | C00026 |
| N00025 | C00027 | proxy(2,8) | N00026, N00027, N00028, N00029 |
| N00026 | none | positive row contradiction | C00028 |
| N00027 | none | positive row contradiction | C00029 |
| N00028 | none | positive row contradiction | C00030 |
| N00029 | C00031 | angle(8,-13573/65536) | N00030, N00039 |
| N00030 | C00032 | sat(5,8) | N00031, N00032, N00033, N00034, N00035, N00036, N00037, N00038 |
| N00031 | none | positive row contradiction | C00033 |
| N00032 | none | positive row contradiction | C00034 |
| N00033 | C00035 | positive row contradiction | C00036 |
| N00034 | none | positive row contradiction | C00037 |
| N00035 | none | positive row contradiction | C00038 |
| N00036 | C00039 | positive row contradiction | C00040 |
| N00037 | C00041 | positive row contradiction | C00042 |
| N00038 | none | positive row contradiction | C00043 |
| N00039 | C00044 | angle(4,-5369/32768) | N00040, N00041 |
| N00040 | none | positive row contradiction | C00045 |
| N00041 | C00046 | sat(2,7) | N00042, N00059, N00060, N00061, N00062, N00071, N00072, N00073 |
| N00042 | C00047 | angle(8,-13573/131072) | N00043, N00052 |
| N00043 | C00048 | sat(1,7) | N00044, N00045, N00046, N00047, N00048, N00049, N00050, N00051 |
| N00044 | none | positive row contradiction | C00049 |
| N00045 | none | positive row contradiction | C00050 |
| N00046 | C00051 | positive row contradiction | C00052 |
| N00047 | none | positive row contradiction | C00053 |
| N00048 | none | positive row contradiction | C00054 |
| N00049 | none | positive row contradiction | C00055 |
| N00050 | C00056 | positive row contradiction | C00057 |
| N00051 | none | positive row contradiction | C00058 |
| N00052 | C00059 | proxy(1,4) | N00053, N00054, N00055, N00056 |
| N00053 | none | positive row contradiction | C00060 |
| N00054 | none | positive row contradiction | C00061 |
| N00055 | none | positive row contradiction | C00062 |
| N00056 | C00063 | angle(8,-13573/262144) | N00057, N00058 |
| N00057 | C00064 | positive row contradiction | C00065 |
| N00058 | C00066 | catalogue sharp terminal(2) | C05010 |
| N00059 | none | positive row contradiction | C00067 |
| N00060 | none | positive row contradiction | C00068 |
| N00061 | none | positive row contradiction | C00069 |
| N00062 | C00070 | angle(8,-13573/131072) | N00063, N00064 |
| N00063 | C00071 | positive row contradiction | C00072 |
| N00064 | C00073 | angle(8,-13573/262144) | N00065, N00068 |
| N00065 | C00074 | angle(4,-679/16384) | N00066, N00067 |
| N00066 | C00075 | positive row contradiction | C00076 |
| N00067 | C00077 | positive row contradiction | C00078 |
| N00068 | C00079 | angle(4,-679/16384) | N00069, N00070 |
| N00069 | C00080 | positive row contradiction | C00081 |
| N00070 | C00082 | catalogue sharp terminal(1) | C05011 |
| N00071 | none | positive row contradiction | C00083 |
| N00072 | C00084 | positive row contradiction | C00085 |
| N00073 | none | positive row contradiction | C00086 |
| N00074 | C00087 | angle(7,-13573/65536) | N00075, N00076 |
| N00075 | C00088 | positive row contradiction | C00089 |
| N00076 | C00090 | positive row contradiction | C00091 |
| N00077 | C00092 | angle(6,-13573/65536) | N00078, N00079 |
| N00078 | C00093 | positive row contradiction | C00094 |
| N00079 | C00095 | angle(7,-13573/65536) | N00080, N00089 |
| N00080 | C00096 | proxy(7,8) | N00081, N00082, N00087, N00088 |
| N00081 | none | positive row contradiction | C00097 |
| N00082 | C00098 | proxy(2,8) | N00083, N00084, N00085, N00086 |
| N00083 | C00099 | positive row contradiction | C00100 |
| N00084 | none | positive row contradiction | C00101 |
| N00085 | none | positive row contradiction | C00102 |
| N00086 | none | positive row contradiction | C00103 |
| N00087 | none | positive row contradiction | C00104 |
| N00088 | none | positive row contradiction | C00105 |
| N00089 | C00106 | proxy(7,8) | N00090, N00091, N00092, N00093 |
| N00090 | none | positive row contradiction | C00107 |
| N00091 | C00108 | positive row contradiction | C00109 |
| N00092 | none | positive row contradiction | C00110 |
| N00093 | none | positive row contradiction | C00111 |
| N00094 | C00112 | proxy(5,8) | N00095, N00096, N00097, N00124 |
| N00095 | C00113 | positive row contradiction | C00114 |
| N00096 | C00115 | positive row contradiction | C00116 |
| N00097 | C00117 | proxy(6,8) | N00098, N00121, N00122, N00123 |
| N00098 | C00118 | sat(5,8) | N00099, N00100, N00101, N00104, N00105, N00106, N00107, N00120 |
| N00099 | none | positive row contradiction | C00119 |
| N00100 | none | positive row contradiction | C00120 |
| N00101 | C00121 | angle(4,-13125/65536) | N00102, N00103 |
| N00102 | none | positive row contradiction | C00122 |
| N00103 | C00123 | positive row contradiction | C00124 |
| N00104 | none | positive row contradiction | C00125 |
| N00105 | none | positive row contradiction | C00126 |
| N00106 | none | positive row contradiction | C00127 |
| N00107 | C00128 | angle(4,-13125/65536) | N00108, N00109 |
| N00108 | none | positive row contradiction | C00129 |
| N00109 | C00130 | angle(7,-13573/65536) | N00110, N00111 |
| N00110 | C00131 | positive row contradiction | C00132 |
| N00111 | C00133 | sat(6,8) | N00112, N00113, N00114, N00115, N00116, N00117, N00118, N00119 |
| N00112 | C00134 | positive row contradiction | C00135 |
| N00113 | none | positive row contradiction | C00136 |
| N00114 | none | positive row contradiction | C00137 |
| N00115 | none | positive row contradiction | C00138 |
| N00116 | C00139 | positive row contradiction | C00140 |
| N00117 | none | positive row contradiction | C00141 |
| N00118 | none | positive row contradiction | C00142 |
| N00119 | none | common-axis chain [[8,1],[6,8,5]] | endpoint squared distance < 4 |
| N00120 | none | positive row contradiction | C00143 |
| N00121 | none | positive row contradiction | C00144 |
| N00122 | none | positive row contradiction | C00145 |
| N00123 | none | positive row contradiction | C00146 |
| N00124 | C00147 | angle(6,-13539/65536) | N00125, N00126 |
| N00125 | none | positive row contradiction | C00148 |
| N00126 | C00149 | sat(4,8) | N00127, N00128, N00129, N00130, N00131, N00132, N00133, N00134 |
| N00127 | none | positive row contradiction | C00150 |
| N00128 | C00151 | positive row contradiction | C00152 |
| N00129 | none | positive row contradiction | C00153 |
| N00130 | C00154 | positive row contradiction | C00155 |
| N00131 | none | positive row contradiction | C00156 |
| N00132 | C00157 | positive row contradiction | C00158 |
| N00133 | none | positive row contradiction | C00159 |
| N00134 | C00160 | positive row contradiction | C00161 |
| N00135 | C00162 | angle(3,-13573/65536) | N00136, N00137 |
| N00136 | C00163 | positive row contradiction | C00164 |
| N00137 | C00165 | angle(7,-13573/65536) | N00138, N00209 |
| N00138 | C00166 | proxy(1,8) | N00139, N00140, N00185, N00196 |
| N00139 | none | positive row contradiction | C00167 |
| N00140 | C00168 | angle(4,13573/65536) | N00141, N00184 |
| N00141 | C00169 | proxy(6,8) | N00142, N00143, N00144, N00183 |
| N00142 | C00170 | positive row contradiction | C00171 |
| N00143 | none | positive row contradiction | C00172 |
| N00144 | C00173 | proxy(1,4) | N00145, N00146, N00147, N00148 |
| N00145 | none | positive row contradiction | C00174 |
| N00146 | none | positive row contradiction | C00175 |
| N00147 | none | positive row contradiction | C00176 |
| N00148 | C00177 | angle(8,-13573/65536) | N00149, N00158 |
| N00149 | C00178 | sat(1,8) | N00150, N00151, N00152, N00153, N00154, N00155, N00156, N00157 |
| N00150 | none | positive row contradiction | C00179 |
| N00151 | none | positive row contradiction | C00180 |
| N00152 | none | positive row contradiction | C00181 |
| N00153 | none | positive row contradiction | C00182 |
| N00154 | none | positive row contradiction | C00183 |
| N00155 | none | positive row contradiction | C00184 |
| N00156 | none | positive row contradiction | C00185 |
| N00157 | none | positive row contradiction | C00186 |
| N00158 | C00187 | angle(8,-13573/131072) | N00159, N00164 |
| N00159 | C00188 | proxy(5,8) | N00160, N00161, N00162, N00163 |
| N00160 | none | positive row contradiction | C00189 |
| N00161 | none | positive row contradiction | C00190 |
| N00162 | C00191 | positive row contradiction | C00192 |
| N00163 | none | positive row contradiction | C00193 |
| N00164 | C00194 | sat(1,8) | N00165, N00166, N00169, N00170, N00171, N00172, N00181, N00182 |
| N00165 | none | positive row contradiction | C00195 |
| N00166 | C00196 | angle(8,-13573/262144) | N00167, N00168 |
| N00167 | C00197 | positive row contradiction | C00198 |
| N00168 | C00199 | catalogue sharp terminal(2) | C05003 |
| N00169 | none | positive row contradiction | C00200 |
| N00170 | none | positive row contradiction | C00201 |
| N00171 | none | positive row contradiction | C00202 |
| N00172 | C00203 | sat(0,7) | N00173, N00174, N00175, N00176, N00177, N00178, N00179, N00180 |
| N00173 | none | positive row contradiction | C00204 |
| N00174 | none | positive row contradiction | C00205 |
| N00175 | C00206 | catalogue sharp terminal(2) | C05004 |
| N00176 | none | positive row contradiction | C00207 |
| N00177 | none | positive row contradiction | C00208 |
| N00178 | C00209 | catalogue sharp terminal(2) | C05005 |
| N00179 | none | positive row contradiction | C00210 |
| N00180 | none | positive row contradiction | C00211 |
| N00181 | none | positive row contradiction | C00212 |
| N00182 | none | positive row contradiction | C00213 |
| N00183 | none | positive row contradiction | C00214 |
| N00184 | C00215 | positive row contradiction | C00216 |
| N00185 | C00217 | proxy(7,8) | N00186, N00187, N00194, N00195 |
| N00186 | none | positive row contradiction | C00218 |
| N00187 | C00219 | angle(8,-13573/65536) | N00188, N00189 |
| N00188 | C00220 | positive row contradiction | C00221 |
| N00189 | C00222 | proxy(2,8) | N00190, N00191, N00192, N00193 |
| N00190 | C00223 | positive row contradiction | C00224 |
| N00191 | none | positive row contradiction | C00225 |
| N00192 | none | positive row contradiction | C00226 |
| N00193 | none | positive row contradiction | C00227 |
| N00194 | none | positive row contradiction | C00228 |
| N00195 | none | positive row contradiction | C00229 |
| N00196 | C00230 | angle(6,-13167/65536) | N00197, N00198 |
| N00197 | none | positive row contradiction | C00231 |
| N00198 | C00232 | proxy(5,8) | N00199, N00200, N00201, N00208 |
| N00199 | C00233 | positive row contradiction | C00234 |
| N00200 | C00235 | positive row contradiction | C00236 |
| N00201 | C00237 | angle(4,24799/131072) | N00202, N00207 |
| N00202 | C00238 | proxy(4,8) | N00203, N00204, N00205, N00206 |
| N00203 | none | positive row contradiction | C00239 |
| N00204 | C00240 | positive row contradiction | C00241 |
| N00205 | none | positive row contradiction | C00242 |
| N00206 | none | positive row contradiction | C00243 |
| N00207 | none | positive row contradiction | C00244 |
| N00208 | C00245 | positive row contradiction | C00246 |
| N00209 | C00247 | angle(6,-13573/65536) | N00210, N00211 |
| N00210 | none | positive row contradiction | C00248 |
| N00211 | C00249 | proxy(1,8) | N00212, N00213, N00262, N00267 |
| N00212 | none | positive row contradiction | C00250 |
| N00213 | C00251 | angle(4,13573/65536) | N00214, N00261 |
| N00214 | C00252 | proxy(2,8) | N00215, N00216, N00217, N00218 |
| N00215 | none | positive row contradiction | C00253 |
| N00216 | none | positive row contradiction | C00254 |
| N00217 | none | positive row contradiction | C00255 |
| N00218 | C00256 | angle(8,-13573/65536) | N00219, N00232 |
| N00219 | C00257 | sat(1,8) | N00220, N00221, N00222, N00223, N00224, N00225, N00226, N00227 |
| N00220 | none | positive row contradiction | C00258 |
| N00221 | C00259 | positive row contradiction | C00260 |
| N00222 | none | positive row contradiction | C00261 |
| N00223 | C00262 | positive row contradiction | C00263 |
| N00224 | none | positive row contradiction | C00264 |
| N00225 | C00265 | positive row contradiction | C00266 |
| N00226 | none | positive row contradiction | C00267 |
| N00227 | C00268 | proxy(5,8) | N00228, N00229, N00230, N00231 |
| N00228 | none | positive row contradiction | C00269 |
| N00229 | none | positive row contradiction | C00270 |
| N00230 | C00271 | positive row contradiction | C00272 |
| N00231 | none | positive row contradiction | C00273 |
| N00232 | C00274 | sat(1,8) | N00233, N00234, N00245, N00246, N00247, N00248, N00259, N00260 |
| N00233 | none | positive row contradiction | C00275 |
| N00234 | C00276 | angle(8,-13573/131072) | N00235, N00236 |
| N00235 | C00277 | positive row contradiction | C00278 |
| N00236 | C00279 | proxy(5,8) | N00237, N00238, N00239, N00244 |
| N00237 | none | positive row contradiction | C00280 |
| N00238 | none | positive row contradiction | C00281 |
| N00239 | C00282 | proxy(6,8) | N00240, N00241, N00242, N00243 |
| N00240 | none | positive row contradiction | C00283 |
| N00241 | none | positive row contradiction | C00284 |
| N00242 | C00285 | catalogue sharp terminal(1) | C05012 |
| N00243 | none | positive row contradiction | C00286 |
| N00244 | none | positive row contradiction | C00287 |
| N00245 | none | positive row contradiction | C00288 |
| N00246 | C00289 | positive row contradiction | C00290 |
| N00247 | none | positive row contradiction | C00291 |
| N00248 | C00292 | angle(8,-13573/131072) | N00249, N00250 |
| N00249 | C00293 | positive row contradiction | C00294 |
| N00250 | C00295 | proxy(5,8) | N00251, N00252, N00253, N00258 |
| N00251 | none | positive row contradiction | C00296 |
| N00252 | none | positive row contradiction | C00297 |
| N00253 | C00298 | proxy(6,8) | N00254, N00255, N00256, N00257 |
| N00254 | none | positive row contradiction | C00299 |
| N00255 | none | positive row contradiction | C00300 |
| N00256 | C00301 | catalogue sharp terminal(3) | C05013 |
| N00257 | none | positive row contradiction | C00302 |
| N00258 | none | positive row contradiction | C00303 |
| N00259 | none | positive row contradiction | C00304 |
| N00260 | C00305 | positive row contradiction | C00306 |
| N00261 | none | positive row contradiction | C00307 |
| N00262 | C00308 | proxy(7,8) | N00263, N00264, N00265, N00266 |
| N00263 | none | positive row contradiction | C00309 |
| N00264 | C00310 | positive row contradiction | C00311 |
| N00265 | none | positive row contradiction | C00312 |
| N00266 | none | positive row contradiction | C00313 |
| N00267 | C00314 | proxy(5,8) | N00268, N00269, N00270, N00279 |
| N00268 | C00315 | positive row contradiction | C00316 |
| N00269 | C00317 | positive row contradiction | C00318 |
| N00270 | C00319 | angle(4,24781/131072) | N00271, N00278 |
| N00271 | C00320 | proxy(6,8) | N00272, N00275, N00276, N00277 |
| N00272 | C00321 | angle(8,-27221/131072) | N00273, N00274 |
| N00273 | C00322 | positive row contradiction | C00323 |
| N00274 | C00324 | positive row contradiction | C00325 |
| N00275 | none | positive row contradiction | C00326 |
| N00276 | none | positive row contradiction | C00327 |
| N00277 | none | positive row contradiction | C00328 |
| N00278 | none | positive row contradiction | C00329 |
| N00279 | C00330 | angle(8,-13573/65536) | N00280, N00281 |
| N00280 | none | positive row contradiction | C00331 |
| N00281 | C00332 | positive row contradiction | C00333 |
| N00282 | C00334 | angle(4,0) | N00283, N00436 |
| N00283 | C00335 | angle(3,-13573/65536) | N00284, N00285 |
| N00284 | C00336 | positive row contradiction | C00337 |
| N00285 | C00338 | angle(2,20839/131072) | N00286, N00435 |
| N00286 | C00339 | angle(4,-13573/65536) | N00287, N00288 |
| N00287 | C00340 | positive row contradiction | C00341 |
| N00288 | C00342 | proxy(1,8) | N00289, N00290, N00367, N00376 |
| N00289 | none | positive row contradiction | C00343 |
| N00290 | C00344 | angle(8,-13573/65536) | N00291, N00332 |
| N00291 | C00345 | angle(7,-13573/65536) | N00292, N00319 |
| N00292 | C00346 | angle(8,-40719/131072) | N00293, N00302 |
| N00293 | C00347 | proxy(2,8) | N00294, N00295, N00296, N00297 |
| N00294 | none | positive row contradiction | C00348 |
| N00295 | none | positive row contradiction | C00349 |
| N00296 | none | positive row contradiction | C00350 |
| N00297 | C00351 | proxy(5,8) | N00298, N00299, N00300, N00301 |
| N00298 | none | positive row contradiction | C00352 |
| N00299 | none | positive row contradiction | C00353 |
| N00300 | C00354 | positive row contradiction | C00355 |
| N00301 | none | positive row contradiction | C00356 |
| N00302 | C00357 | proxy(2,8) | N00303, N00304, N00305, N00306 |
| N00303 | none | positive row contradiction | C00358 |
| N00304 | none | positive row contradiction | C00359 |
| N00305 | none | positive row contradiction | C00360 |
| N00306 | C00361 | proxy(5,8) | N00307, N00308, N00309, N00318 |
| N00307 | none | positive row contradiction | C00362 |
| N00308 | none | positive row contradiction | C00363 |
| N00309 | C00364 | sat(5,8) | N00310, N00311, N00312, N00313, N00314, N00315, N00316, N00317 |
| N00310 | none | positive row contradiction | C00365 |
| N00311 | none | positive row contradiction | C00366 |
| N00312 | C00367 | positive row contradiction | C00368 |
| N00313 | none | positive row contradiction | C00369 |
| N00314 | none | positive row contradiction | C00370 |
| N00315 | none | positive row contradiction | C00371 |
| N00316 | C00372 | positive row contradiction | C00373 |
| N00317 | none | positive row contradiction | C00374 |
| N00318 | none | positive row contradiction | C00375 |
| N00319 | C00376 | proxy(6,8) | N00320, N00321, N00322, N00331 |
| N00320 | none | positive row contradiction | C00377 |
| N00321 | none | positive row contradiction | C00378 |
| N00322 | C00379 | sat(1,8) | N00323, N00324, N00325, N00326, N00327, N00328, N00329, N00330 |
| N00323 | none | positive row contradiction | C00380 |
| N00324 | C00381 | positive row contradiction | C00382 |
| N00325 | none | positive row contradiction | C00383 |
| N00326 | none | positive row contradiction | C00384 |
| N00327 | none | positive row contradiction | C00385 |
| N00328 | C00386 | positive row contradiction | C00387 |
| N00329 | none | positive row contradiction | C00388 |
| N00330 | none | positive row contradiction | C00389 |
| N00331 | none | positive row contradiction | C00390 |
| N00332 | C00391 | proxy(5,8) | N00333, N00334, N00339, N00366 |
| N00333 | none | positive row contradiction | C00392 |
| N00334 | C00393 | proxy(2,8) | N00335, N00336, N00337, N00338 |
| N00335 | none | positive row contradiction | C00394 |
| N00336 | none | positive row contradiction | C00395 |
| N00337 | none | positive row contradiction | C00396 |
| N00338 | C00397 | positive row contradiction | C00398 |
| N00339 | C00399 | angle(7,-13573/65536) | N00340, N00353 |
| N00340 | C00400 | proxy(2,8) | N00341, N00342, N00343, N00344 |
| N00341 | none | positive row contradiction | C00401 |
| N00342 | none | positive row contradiction | C00402 |
| N00343 | none | positive row contradiction | C00403 |
| N00344 | C00404 | proxy(6,8) | N00345, N00346, N00347, N00352 |
| N00345 | none | positive row contradiction | C00405 |
| N00346 | none | positive row contradiction | C00406 |
| N00347 | C00407 | angle(8,-13573/131072) | N00348, N00349 |
| N00348 | C00408 | positive row contradiction | C00409 |
| N00349 | C00410 | angle(8,-13573/262144) | N00350, N00351 |
| N00350 | C00411 | positive row contradiction | C00412 |
| N00351 | C00413 | catalogue sharp terminal(1) | C05014 |
| N00352 | none | positive row contradiction | C00414 |
| N00353 | C00415 | proxy(2,8) | N00354, N00355, N00356, N00357 |
| N00354 | none | positive row contradiction | C00416 |
| N00355 | none | positive row contradiction | C00417 |
| N00356 | none | positive row contradiction | C00418 |
| N00357 | C00419 | proxy(6,8) | N00358, N00359, N00360, N00365 |
| N00358 | none | positive row contradiction | C00420 |
| N00359 | none | positive row contradiction | C00421 |
| N00360 | C00422 | angle(8,-13573/131072) | N00361, N00362 |
| N00361 | C00423 | positive row contradiction | C00424 |
| N00362 | C00425 | angle(8,-13573/262144) | N00363, N00364 |
| N00363 | C00426 | positive row contradiction | C00427 |
| N00364 | C00428 | catalogue sharp terminal(1) | C05015 |
| N00365 | none | positive row contradiction | C00429 |
| N00366 | C00430 | positive row contradiction | C00431 |
| N00367 | C00432 | proxy(7,8) | N00368, N00369, N00374, N00375 |
| N00368 | none | positive row contradiction | C00433 |
| N00369 | C00434 | proxy(2,8) | N00370, N00371, N00372, N00373 |
| N00370 | C00435 | positive row contradiction | C00436 |
| N00371 | none | positive row contradiction | C00437 |
| N00372 | none | positive row contradiction | C00438 |
| N00373 | none | positive row contradiction | C00439 |
| N00374 | none | positive row contradiction | C00440 |
| N00375 | none | positive row contradiction | C00441 |
| N00376 | C00442 | angle(8,-13573/65536) | N00377, N00400 |
| N00377 | C00443 | proxy(5,8) | N00378, N00379, N00380, N00399 |
| N00378 | C00444 | positive row contradiction | C00445 |
| N00379 | C00446 | positive row contradiction | C00447 |
| N00380 | C00448 | angle(7,-13573/65536) | N00381, N00390 |
| N00381 | C00449 | sat(6,8) | N00382, N00383, N00384, N00385, N00386, N00387, N00388, N00389 |
| N00382 | C00450 | positive row contradiction | C00451 |
| N00383 | none | positive row contradiction | C00452 |
| N00384 | none | positive row contradiction | C00453 |
| N00385 | none | positive row contradiction | C00454 |
| N00386 | C00455 | positive row contradiction | C00456 |
| N00387 | none | positive row contradiction | C00457 |
| N00388 | none | positive row contradiction | C00458 |
| N00389 | none | positive row contradiction | C00459 |
| N00390 | C00460 | sat(5,8) | N00391, N00392, N00393, N00394, N00395, N00396, N00397, N00398 |
| N00391 | none | positive row contradiction | C00461 |
| N00392 | none | positive row contradiction | C00462 |
| N00393 | none | positive row contradiction | C00463 |
| N00394 | none | positive row contradiction | C00464 |
| N00395 | none | positive row contradiction | C00465 |
| N00396 | none | positive row contradiction | C00466 |
| N00397 | C00467 | positive row contradiction | C00468 |
| N00398 | none | positive row contradiction | C00469 |
| N00399 | C00470 | positive row contradiction | C00471 |
| N00400 | C00472 | proxy(5,8) | N00401, N00402, N00403, N00432 |
| N00401 | C00473 | positive row contradiction | C00474 |
| N00402 | C00475 | positive row contradiction | C00476 |
| N00403 | C00477 | proxy(6,8) | N00404, N00429, N00430, N00431 |
| N00404 | C00478 | sat(6,8) | N00405, N00414, N00415, N00416, N00417, N00426, N00427, N00428 |
| N00405 | C00479 | sat(2,7) | N00406, N00407, N00408, N00409, N00410, N00411, N00412, N00413 |
| N00406 | C00480 | positive row contradiction | C00481 |
| N00407 | none | positive row contradiction | C00482 |
| N00408 | none | positive row contradiction | C00483 |
| N00409 | none | positive row contradiction | C00484 |
| N00410 | none | positive row contradiction | C00485 |
| N00411 | none | positive row contradiction | C00486 |
| N00412 | none | positive row contradiction | C00487 |
| N00413 | none | positive row contradiction | C00488 |
| N00414 | none | positive row contradiction | C00489 |
| N00415 | none | positive row contradiction | C00490 |
| N00416 | none | positive row contradiction | C00491 |
| N00417 | C00492 | sat(4,8) | N00418, N00419, N00420, N00421, N00422, N00423, N00424, N00425 |
| N00418 | none | positive row contradiction | C00493 |
| N00419 | C00494 | positive row contradiction | C00495 |
| N00420 | none | positive row contradiction | C00496 |
| N00421 | none | positive row contradiction | C00497 |
| N00422 | none | positive row contradiction | C00498 |
| N00423 | C00499 | positive row contradiction | C00500 |
| N00424 | none | positive row contradiction | C00501 |
| N00425 | none | positive row contradiction | C00502 |
| N00426 | none | positive row contradiction | C00503 |
| N00427 | none | positive row contradiction | C00504 |
| N00428 | none | positive row contradiction | C00505 |
| N00429 | none | positive row contradiction | C00506 |
| N00430 | none | positive row contradiction | C00507 |
| N00431 | none | positive row contradiction | C00508 |
| N00432 | C00509 | angle(7,-12997/65536) | N00433, N00434 |
| N00433 | none | positive row contradiction | C00510 |
| N00434 | C00511 | positive row contradiction | C00512 |
| N00435 | C00513 | positive row contradiction | C00514 |
| N00436 | C00515 | angle(3,-13573/65536) | N00437, N00438 |
| N00437 | C00516 | positive row contradiction | C00517 |
| N00438 | C00518 | proxy(1,8) | N00439, N00440, N00541, N00558 |
| N00439 | none | positive row contradiction | C00519 |
| N00440 | C00520 | angle(4,13573/65536) | N00441, N00536 |
| N00441 | C00521 | proxy(6,8) | N00442, N00443, N00444, N00535 |
| N00442 | C00522 | positive row contradiction | C00523 |
| N00443 | none | positive row contradiction | C00524 |
| N00444 | C00525 | sat(2,7) | N00445, N00492, N00493, N00494, N00495, N00532, N00533, N00534 |
| N00445 | C00526 | proxy(1,4) | N00446, N00447, N00448, N00449 |
| N00446 | none | positive row contradiction | C00527 |
| N00447 | none | positive row contradiction | C00528 |
| N00448 | none | positive row contradiction | C00529 |
| N00449 | C00530 | proxy(5,8) | N00450, N00451, N00452, N00491 |
| N00450 | none | positive row contradiction | C00531 |
| N00451 | C00532 | positive row contradiction | C00533 |
| N00452 | C00534 | sat(5,8) | N00453, N00454, N00455, N00470, N00471, N00472, N00475, N00490 |
| N00453 | none | positive row contradiction | C00535 |
| N00454 | none | positive row contradiction | C00536 |
| N00455 | C00537 | sat(1,8) | N00456, N00457, N00460, N00461, N00462, N00463, N00468, N00469 |
| N00456 | none | positive row contradiction | C00538 |
| N00457 | C00539 | angle(8,-10745/131072) | N00458, N00459 |
| N00458 | none | positive row contradiction | C00540 |
| N00459 | C00541 | catalogue sharp terminal(1) | C05006 |
| N00460 | none | positive row contradiction | C00542 |
| N00461 | none | positive row contradiction | C00543 |
| N00462 | none | positive row contradiction | C00544 |
| N00463 | C00545 | angle(8,-15067/131072) | N00464, N00465 |
| N00464 | none | positive row contradiction | C00546 |
| N00465 | C00547 | angle(8,-643/16384) | N00466, N00467 |
| N00466 | none | positive row contradiction | C00548 |
| N00467 | C00549 | uniform sharp terminal | C04997 |
| N00468 | none | positive row contradiction | C00550 |
| N00469 | none | positive row contradiction | C00551 |
| N00470 | none | positive row contradiction | C00552 |
| N00471 | none | positive row contradiction | C00553 |
| N00472 | C00554 | angle(8,-27255/131072) | N00473, N00474 |
| N00473 | C00555 | positive row contradiction | C00556 |
| N00474 | C00557 | positive row contradiction | C00558 |
| N00475 | C00559 | sat(1,8) | N00476, N00477, N00480, N00481, N00482, N00483, N00488, N00489 |
| N00476 | none | positive row contradiction | C00560 |
| N00477 | C00561 | angle(8,-9829/131072) | N00478, N00479 |
| N00478 | none | positive row contradiction | C00562 |
| N00479 | C00563 | catalogue sharp terminal(1) | C05007 |
| N00480 | none | positive row contradiction | C00564 |
| N00481 | none | positive row contradiction | C00565 |
| N00482 | none | positive row contradiction | C00566 |
| N00483 | C00567 | angle(8,-6763/65536) | N00484, N00485 |
| N00484 | none | positive row contradiction | C00568 |
| N00485 | C00569 | angle(8,-4795/131072) | N00486, N00487 |
| N00486 | none | positive row contradiction | C00570 |
| N00487 | C00571 | uniform sharp terminal | C04998 |
| N00488 | none | positive row contradiction | C00572 |
| N00489 | none | positive row contradiction | C00573 |
| N00490 | none | positive row contradiction | C00574 |
| N00491 | none | positive row contradiction | C00575 |
| N00492 | none | positive row contradiction | C00576 |
| N00493 | none | positive row contradiction | C00577 |
| N00494 | none | positive row contradiction | C00578 |
| N00495 | C00579 | sat(1,8) | N00496, N00497, N00516, N00517, N00518, N00519, N00530, N00531 |
| N00496 | none | positive row contradiction | C00580 |
| N00497 | C00581 | angle(8,-13573/65536) | N00498, N00499 |
| N00498 | none | positive row contradiction | C00582 |
| N00499 | C00583 | proxy(5,8) | N00500, N00501, N00502, N00515 |
| N00500 | none | positive row contradiction | C00584 |
| N00501 | none | positive row contradiction | C00585 |
| N00502 | C00586 | sat(1,7) | N00503, N00504, N00505, N00508, N00509, N00510, N00511, N00514 |
| N00503 | none | positive row contradiction | C00587 |
| N00504 | none | positive row contradiction | C00588 |
| N00505 | C00589 | angle(4,2719/65536) | N00506, N00507 |
| N00506 | C00590 | uniform sharp terminal | C04999 |
| N00507 | C00591 | positive row contradiction | C00592 |
| N00508 | none | positive row contradiction | C00593 |
| N00509 | none | positive row contradiction | C00594 |
| N00510 | none | common-axis chain [[7,0],[1,7,2]] | endpoint squared distance < 4 |
| N00511 | C00595 | angle(4,2719/65536) | N00512, N00513 |
| N00512 | C00596 | uniform sharp terminal | C05000 |
| N00513 | C00597 | positive row contradiction | C00598 |
| N00514 | none | positive row contradiction | C00599 |
| N00515 | none | positive row contradiction | C00600 |
| N00516 | none | positive row contradiction | C00601 |
| N00517 | none | positive row contradiction | C00602 |
| N00518 | none | positive row contradiction | C00603 |
| N00519 | C00604 | angle(8,-13573/65536) | N00520, N00521 |
| N00520 | C00605 | positive row contradiction | C00606 |
| N00521 | C00607 | proxy(5,8) | N00522, N00523, N00524, N00529 |
| N00522 | none | positive row contradiction | C00608 |
| N00523 | none | positive row contradiction | C00609 |
| N00524 | C00610 | angle(8,-11515/131072) | N00525, N00526 |
| N00525 | none | positive row contradiction | C00611 |
| N00526 | C00612 | angle(4,2719/65536) | N00527, N00528 |
| N00527 | C00613 | catalogue sharp terminal(1) | C05008 |
| N00528 | C00614 | positive row contradiction | C00615 |
| N00529 | none | positive row contradiction | C00616 |
| N00530 | none | positive row contradiction | C00617 |
| N00531 | C00618 | positive row contradiction | C00619 |
| N00532 | none | positive row contradiction | C00620 |
| N00533 | C00621 | positive row contradiction | C00622 |
| N00534 | none | positive row contradiction | C00623 |
| N00535 | none | positive row contradiction | C00624 |
| N00536 | C00625 | proxy(5,8) | N00537, N00538, N00539, N00540 |
| N00537 | none | positive row contradiction | C00626 |
| N00538 | C00627 | positive row contradiction | C00628 |
| N00539 | C00629 | positive row contradiction | C00630 |
| N00540 | C00631 | positive row contradiction | C00632 |
| N00541 | C00633 | angle(6,-13573/65536) | N00542, N00543 |
| N00542 | none | positive row contradiction | C00634 |
| N00543 | C00635 | angle(7,-13573/65536) | N00544, N00551 |
| N00544 | C00636 | proxy(7,8) | N00545, N00546, N00549, N00550 |
| N00545 | none | positive row contradiction | C00637 |
| N00546 | C00638 | angle(8,-13573/65536) | N00547, N00548 |
| N00547 | none | positive row contradiction | C00639 |
| N00548 | C00640 | positive row contradiction | C00641 |
| N00549 | none | positive row contradiction | C00642 |
| N00550 | none | positive row contradiction | C00643 |
| N00551 | C00644 | proxy(2,8) | N00552, N00555, N00556, N00557 |
| N00552 | C00645 | angle(8,-13573/65536) | N00553, N00554 |
| N00553 | C00646 | positive row contradiction | C00647 |
| N00554 | C00648 | positive row contradiction | C00649 |
| N00555 | none | positive row contradiction | C00650 |
| N00556 | none | positive row contradiction | C00651 |
| N00557 | none | positive row contradiction | C00652 |
| N00558 | C00653 | angle(6,-13573/65536) | N00559, N00560 |
| N00559 | none | positive row contradiction | C00654 |
| N00560 | C00655 | proxy(5,8) | N00561, N00562, N00563, N00586 |
| N00561 | C00656 | positive row contradiction | C00657 |
| N00562 | C00658 | positive row contradiction | C00659 |
| N00563 | C00660 | sat(5,8) | N00564, N00565, N00566, N00571, N00572, N00573, N00574, N00585 |
| N00564 | C00661 | positive row contradiction | C00662 |
| N00565 | C00663 | positive row contradiction | C00664 |
| N00566 | C00665 | proxy(6,8) | N00567, N00568, N00569, N00570 |
| N00567 | C00666 | positive row contradiction | C00667 |
| N00568 | none | positive row contradiction | C00668 |
| N00569 | none | positive row contradiction | C00669 |
| N00570 | none | positive row contradiction | C00670 |
| N00571 | none | positive row contradiction | C00671 |
| N00572 | none | positive row contradiction | C00672 |
| N00573 | C00673 | positive row contradiction | C00674 |
| N00574 | C00675 | angle(8,-13573/65536) | N00575, N00578 |
| N00575 | C00676 | angle(7,-13573/65536) | N00576, N00577 |
| N00576 | none | positive row contradiction | C00677 |
| N00577 | none | positive row contradiction | C00678 |
| N00578 | C00679 | angle(7,-3357/16384) | N00579, N00580 |
| N00579 | C00680 | positive row contradiction | C00681 |
| N00580 | C00682 | proxy(4,8) | N00581, N00582, N00583, N00584 |
| N00581 | none | positive row contradiction | C00683 |
| N00582 | C00684 | positive row contradiction | C00685 |
| N00583 | none | positive row contradiction | C00686 |
| N00584 | none | positive row contradiction | C00687 |
| N00585 | none | positive row contradiction | C00688 |
| N00586 | C00689 | sat(2,7) | N00587, N00588, N00589, N00590, N00591, N00592, N00593, N00594 |
| N00587 | C00690 | positive row contradiction | C00691 |
| N00588 | none | positive row contradiction | C00692 |
| N00589 | none | positive row contradiction | C00693 |
| N00590 | none | positive row contradiction | C00694 |
| N00591 | C00695 | positive row contradiction | C00696 |
| N00592 | none | positive row contradiction | C00697 |
| N00593 | none | positive row contradiction | C00698 |
| N00594 | none | positive row contradiction | C00699 |
| N00595 | C00700 | angle(4,0) | N00596, N00975 |
| N00596 | C00701 | angle(5,0) | N00597, N00750 |
| N00597 | C00702 | angle(2,13573/65536) | N00598, N00747 |
| N00598 | C00703 | proxy(1,8) | N00599, N00600, N00675, N00684 |
| N00599 | none | positive row contradiction | C00704 |
| N00600 | C00705 | proxy(5,8) | N00601, N00602, N00609, N00672 |
| N00601 | none | positive row contradiction | C00706 |
| N00602 | C00707 | angle(6,25527/131072) | N00603, N00608 |
| N00603 | C00708 | proxy(6,8) | N00604, N00605, N00606, N00607 |
| N00604 | none | positive row contradiction | C00709 |
| N00605 | none | positive row contradiction | C00710 |
| N00606 | C00711 | positive row contradiction | C00712 |
| N00607 | none | positive row contradiction | C00713 |
| N00608 | none | positive row contradiction | C00714 |
| N00609 | C00715 | angle(4,-13573/65536) | N00610, N00611 |
| N00610 | none | positive row contradiction | C00716 |
| N00611 | C00717 | angle(6,2629/16384) | N00612, N00671 |
| N00612 | C00718 | proxy(0,7) | N00613, N00614, N00639, N00670 |
| N00613 | none | positive row contradiction | C00719 |
| N00614 | C00720 | proxy(6,8) | N00615, N00616, N00617, N00638 |
| N00615 | none | positive row contradiction | C00721 |
| N00616 | none | positive row contradiction | C00722 |
| N00617 | C00723 | proxy(1,4) | N00618, N00619, N00620, N00621 |
| N00618 | none | positive row contradiction | C00724 |
| N00619 | none | positive row contradiction | C00725 |
| N00620 | none | positive row contradiction | C00726 |
| N00621 | C00727 | angle(8,-13573/65536) | N00622, N00623 |
| N00622 | C00728 | positive row contradiction | C00729 |
| N00623 | C00730 | angle(8,-13573/131072) | N00624, N00633 |
| N00624 | C00731 | sat(5,8) | N00625, N00626, N00627, N00628, N00629, N00630, N00631, N00632 |
| N00625 | none | positive row contradiction | C00732 |
| N00626 | none | positive row contradiction | C00733 |
| N00627 | C00734 | positive row contradiction | C00735 |
| N00628 | none | positive row contradiction | C00736 |
| N00629 | none | positive row contradiction | C00737 |
| N00630 | none | positive row contradiction | C00738 |
| N00631 | C00739 | positive row contradiction | C00740 |
| N00632 | none | positive row contradiction | C00741 |
| N00633 | C00742 | angle(8,-13573/262144) | N00634, N00637 |
| N00634 | C00743 | angle(7,-13573/65536) | N00635, N00636 |
| N00635 | C00744 | positive row contradiction | C00745 |
| N00636 | C00746 | positive row contradiction | C00747 |
| N00637 | C00748 | catalogue sharp terminal(2) | C05016 |
| N00638 | none | positive row contradiction | C00749 |
| N00639 | C00750 | proxy(2,8) | N00640, N00641, N00642, N00643 |
| N00640 | none | positive row contradiction | C00751 |
| N00641 | none | positive row contradiction | C00752 |
| N00642 | none | positive row contradiction | C00753 |
| N00643 | C00754 | sat(2,8) | N00644, N00645, N00646, N00647, N00658, N00659, N00660, N00661 |
| N00644 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N00645 | none | positive row contradiction | C00755 |
| N00646 | none | positive row contradiction | C00756 |
| N00647 | C00757 | proxy(1,4) | N00648, N00649, N00650, N00651 |
| N00648 | none | positive row contradiction | C00758 |
| N00649 | none | positive row contradiction | C00759 |
| N00650 | none | positive row contradiction | C00760 |
| N00651 | C00761 | angle(8,-3147/16384) | N00652, N00653 |
| N00652 | none | positive row contradiction | C00762 |
| N00653 | C00763 | angle(8,-3147/32768) | N00654, N00655 |
| N00654 | C00764 | positive row contradiction | C00765 |
| N00655 | C00766 | angle(8,-3147/65536) | N00656, N00657 |
| N00656 | C00767 | positive row contradiction | C00768 |
| N00657 | C00769 | catalogue sharp terminal(1) | C05018 |
| N00658 | none | positive row contradiction | C00770 |
| N00659 | none | positive row contradiction | C00771 |
| N00660 | none | positive row contradiction | C00772 |
| N00661 | C00773 | angle(8,-10223/65536) | N00662, N00663 |
| N00662 | C00774 | positive row contradiction | C00775 |
| N00663 | C00776 | proxy(6,8) | N00664, N00665, N00666, N00669 |
| N00664 | none | positive row contradiction | C00777 |
| N00665 | none | positive row contradiction | C00778 |
| N00666 | C00779 | angle(8,-7769/131072) | N00667, N00668 |
| N00667 | C00780 | positive row contradiction | C00781 |
| N00668 | C00782 | catalogue sharp terminal(1) | C05017 |
| N00669 | none | positive row contradiction | C00783 |
| N00670 | none | positive row contradiction | C00784 |
| N00671 | none | positive row contradiction | C00785 |
| N00672 | C00786 | angle(6,25527/131072) | N00673, N00674 |
| N00673 | C00787 | positive row contradiction | C00788 |
| N00674 | none | positive row contradiction | C00789 |
| N00675 | C00790 | proxy(7,8) | N00676, N00677, N00682, N00683 |
| N00676 | none | positive row contradiction | C00791 |
| N00677 | C00792 | angle(6,25527/131072) | N00678, N00681 |
| N00678 | C00793 | angle(4,-13089/65536) | N00679, N00680 |
| N00679 | none | positive row contradiction | C00794 |
| N00680 | C00795 | positive row contradiction | C00796 |
| N00681 | none | positive row contradiction | C00797 |
| N00682 | none | positive row contradiction | C00798 |
| N00683 | none | positive row contradiction | C00799 |
| N00684 | C00800 | proxy(5,8) | N00685, N00686, N00687, N00734 |
| N00685 | C00801 | positive row contradiction | C00802 |
| N00686 | C00803 | positive row contradiction | C00804 |
| N00687 | C00805 | sat(2,7) | N00688, N00715, N00716, N00717, N00718, N00731, N00732, N00733 |
| N00688 | C00806 | sat(5,8) | N00689, N00690, N00691, N00692, N00693, N00694, N00695, N00714 |
| N00689 | none | positive row contradiction | C00807 |
| N00690 | C00808 | positive row contradiction | C00809 |
| N00691 | C00810 | positive row contradiction | C00811 |
| N00692 | none | positive row contradiction | C00812 |
| N00693 | none | positive row contradiction | C00813 |
| N00694 | C00814 | positive row contradiction | C00815 |
| N00695 | C00816 | angle(7,-13573/65536) | N00696, N00701 |
| N00696 | C00817 | proxy(4,8) | N00697, N00698, N00699, N00700 |
| N00697 | none | positive row contradiction | C00818 |
| N00698 | C00819 | positive row contradiction | C00820 |
| N00699 | none | positive row contradiction | C00821 |
| N00700 | none | positive row contradiction | C00822 |
| N00701 | C00823 | proxy(6,8) | N00702, N00711, N00712, N00713 |
| N00702 | C00824 | sat(1,8) | N00703, N00704, N00705, N00706, N00707, N00708, N00709, N00710 |
| N00703 | none | positive row contradiction | C00825 |
| N00704 | none | positive row contradiction | C00826 |
| N00705 | none | positive row contradiction | C00827 |
| N00706 | none | positive row contradiction | C00828 |
| N00707 | none | positive row contradiction | C00829 |
| N00708 | none | positive row contradiction | C00830 |
| N00709 | none | positive row contradiction | C00831 |
| N00710 | none | positive row contradiction | C00832 |
| N00711 | none | positive row contradiction | C00833 |
| N00712 | none | positive row contradiction | C00834 |
| N00713 | none | positive row contradiction | C00835 |
| N00714 | none | positive row contradiction | C00836 |
| N00715 | none | positive row contradiction | C00837 |
| N00716 | none | positive row contradiction | C00838 |
| N00717 | none | positive row contradiction | C00839 |
| N00718 | C00840 | proxy(4,8) | N00719, N00720, N00729, N00730 |
| N00719 | none | positive row contradiction | C00841 |
| N00720 | C00842 | sat(5,8) | N00721, N00722, N00723, N00724, N00725, N00726, N00727, N00728 |
| N00721 | none | positive row contradiction | C00843 |
| N00722 | none | positive row contradiction | C00844 |
| N00723 | none | positive row contradiction | C00845 |
| N00724 | none | positive row contradiction | C00846 |
| N00725 | none | positive row contradiction | C00847 |
| N00726 | C00848 | positive row contradiction | C00849 |
| N00727 | C00850 | positive row contradiction | C00851 |
| N00728 | none | positive row contradiction | C00852 |
| N00729 | none | positive row contradiction | C00853 |
| N00730 | none | positive row contradiction | C00854 |
| N00731 | none | positive row contradiction | C00855 |
| N00732 | C00856 | positive row contradiction | C00857 |
| N00733 | none | positive row contradiction | C00858 |
| N00734 | C00859 | proxy(6,8) | N00735, N00744, N00745, N00746 |
| N00735 | C00860 | sat(2,7) | N00736, N00737, N00738, N00739, N00740, N00741, N00742, N00743 |
| N00736 | none | positive row contradiction | C00861 |
| N00737 | none | positive row contradiction | C00862 |
| N00738 | none | positive row contradiction | C00863 |
| N00739 | none | positive row contradiction | C00864 |
| N00740 | none | positive row contradiction | C00865 |
| N00741 | none | positive row contradiction | C00866 |
| N00742 | none | positive row contradiction | C00867 |
| N00743 | none | positive row contradiction | C00868 |
| N00744 | none | positive row contradiction | C00869 |
| N00745 | none | positive row contradiction | C00870 |
| N00746 | none | positive row contradiction | C00871 |
| N00747 | C00872 | angle(5,-26619/131072) | N00748, N00749 |
| N00748 | C00873 | positive row contradiction | C00874 |
| N00749 | C00875 | positive row contradiction | C00876 |
| N00750 | C00877 | angle(3,-13573/65536) | N00751, N00752 |
| N00751 | C00878 | positive row contradiction | C00879 |
| N00752 | C00880 | proxy(1,8) | N00753, N00754, N00889, N00908 |
| N00753 | none | positive row contradiction | C00881 |
| N00754 | C00882 | angle(6,13573/65536) | N00755, N00888 |
| N00755 | C00883 | sat(2,7) | N00756, N00823, N00824, N00825, N00826, N00881, N00882, N00887 |
| N00756 | C00884 | sat(1,8) | N00757, N00758, N00781, N00782, N00783, N00784, N00811, N00812 |
| N00757 | none | positive row contradiction | C00885 |
| N00758 | C00886 | sat(6,8) | N00759, N00760, N00761, N00768, N00769, N00770, N00771, N00780 |
| N00759 | none | positive row contradiction | C00887 |
| N00760 | none | positive row contradiction | C00888 |
| N00761 | C00889 | angle(8,-13573/65536) | N00762, N00763 |
| N00762 | none | positive row contradiction | C00890 |
| N00763 | C00891 | angle(4,-15473/131072) | N00764, N00765 |
| N00764 | none | positive row contradiction | C00892 |
| N00765 | C00893 | angle(4,-937/16384) | N00766, N00767 |
| N00766 | C00894 | positive row contradiction | C00895 |
| N00767 | C00896 | catalogue sharp terminal(1) | C05002 |
| N00768 | none | positive row contradiction | C00897 |
| N00769 | none | positive row contradiction | C00898 |
| N00770 | C00899 | positive row contradiction | C00900 |
| N00771 | C00901 | angle(4,-22187/131072) | N00772, N00773 |
| N00772 | none | positive row contradiction | C00902 |
| N00773 | C00903 | angle(8,-13573/65536) | N00774, N00775 |
| N00774 | none | positive row contradiction | C00904 |
| N00775 | C00905 | angle(8,-13573/131072) | N00776, N00777 |
| N00776 | none | positive row contradiction | C00906 |
| N00777 | C00907 | angle(4,-6947/131072) | N00778, N00779 |
| N00778 | C00908 | positive row contradiction | C00909 |
| N00779 | C00910 | catalogue sharp terminal(1) | C05009 |
| N00780 | none | positive row contradiction | C00911 |
| N00781 | C00912 | positive row contradiction | C00913 |
| N00782 | C00914 | positive row contradiction | C00915 |
| N00783 | none | positive row contradiction | C00916 |
| N00784 | C00917 | angle(4,-1643/8192) | N00785, N00786 |
| N00785 | none | positive row contradiction | C00918 |
| N00786 | C00919 | proxy(2,8) | N00787, N00788, N00789, N00790 |
| N00787 | none | positive row contradiction | C00920 |
| N00788 | none | positive row contradiction | C00921 |
| N00789 | none | positive row contradiction | C00922 |
| N00790 | C00923 | proxy(5,8) | N00791, N00792, N00793, N00810 |
| N00791 | none | positive row contradiction | C00924 |
| N00792 | C00925 | positive row contradiction | C00926 |
| N00793 | C00927 | proxy(6,8) | N00794, N00795, N00796, N00809 |
| N00794 | none | positive row contradiction | C00928 |
| N00795 | none | positive row contradiction | C00929 |
| N00796 | C00930 | sat(6,8) | N00797, N00798, N00799, N00802, N00803, N00804, N00805, N00808 |
| N00797 | none | positive row contradiction | C00931 |
| N00798 | none | positive row contradiction | C00932 |
| N00799 | C00933 | angle(4,-5991/131072) | N00800, N00801 |
| N00800 | C00934 | positive row contradiction | C00935 |
| N00801 | C00936 | uniform sharp terminal | C05001 |
| N00802 | none | positive row contradiction | C00937 |
| N00803 | none | positive row contradiction | C00938 |
| N00804 | none | positive row contradiction | C00939 |
| N00805 | C00940 | angle(4,-5991/131072) | N00806, N00807 |
| N00806 | C00941 | positive row contradiction | C00942 |
| N00807 | C00943 | uniform sharp terminal | C05034 |
| N00808 | none | positive row contradiction | C00944 |
| N00809 | none | positive row contradiction | C00945 |
| N00810 | none | positive row contradiction | C00946 |
| N00811 | C00947 | positive row contradiction | C00948 |
| N00812 | C00949 | proxy(5,8) | N00813, N00814, N00819, N00822 |
| N00813 | none | positive row contradiction | C00950 |
| N00814 | C00951 | proxy(6,8) | N00815, N00816, N00817, N00818 |
| N00815 | none | positive row contradiction | C00952 |
| N00816 | none | positive row contradiction | C00953 |
| N00817 | C00954 | positive row contradiction | C00955 |
| N00818 | none | positive row contradiction | C00956 |
| N00819 | C00957 | angle(8,-13573/65536) | N00820, N00821 |
| N00820 | C00958 | positive row contradiction | C00959 |
| N00821 | C00960 | positive row contradiction | C00961 |
| N00822 | C00962 | positive row contradiction | C00963 |
| N00823 | none | positive row contradiction | C00964 |
| N00824 | none | positive row contradiction | C00965 |
| N00825 | none | positive row contradiction | C00966 |
| N00826 | C00967 | proxy(5,8) | N00827, N00828, N00835, N00880 |
| N00827 | none | positive row contradiction | C00968 |
| N00828 | C00969 | proxy(6,8) | N00829, N00830, N00831, N00834 |
| N00829 | none | positive row contradiction | C00970 |
| N00830 | none | positive row contradiction | C00971 |
| N00831 | C00972 | angle(4,-22187/131072) | N00832, N00833 |
| N00832 | none | positive row contradiction | C00973 |
| N00833 | C00974 | positive row contradiction | C00975 |
| N00834 | none | positive row contradiction | C00976 |
| N00835 | C00977 | proxy(6,8) | N00836, N00837, N00838, N00879 |
| N00836 | none | positive row contradiction | C00978 |
| N00837 | none | positive row contradiction | C00979 |
| N00838 | C00980 | angle(8,-13573/65536) | N00839, N00842 |
| N00839 | C00981 | angle(4,-15473/131072) | N00840, N00841 |
| N00840 | none | positive row contradiction | C00982 |
| N00841 | C00983 | positive row contradiction | C00984 |
| N00842 | C00985 | sat(5,8) | N00843, N00844, N00845, N00860, N00861, N00862, N00863, N00878 |
| N00843 | none | positive row contradiction | C00986 |
| N00844 | C00987 | positive row contradiction | C00988 |
| N00845 | C00989 | angle(8,-13573/131072) | N00846, N00855 |
| N00846 | C00990 | sat(1,7) | N00847, N00848, N00849, N00850, N00851, N00852, N00853, N00854 |
| N00847 | none | positive row contradiction | C00991 |
| N00848 | none | positive row contradiction | C00992 |
| N00849 | C00993 | positive row contradiction | C00994 |
| N00850 | none | positive row contradiction | C00995 |
| N00851 | none | positive row contradiction | C00996 |
| N00852 | none | common-axis chain [[7,0],[1,7,2]] | endpoint squared distance < 4 |
| N00853 | C00997 | positive row contradiction | C00998 |
| N00854 | none | positive row contradiction | C00999 |
| N00855 | C01000 | angle(4,-121/2048) | N00856, N00857 |
| N00856 | C01001 | positive row contradiction | C01002 |
| N00857 | C01003 | angle(8,-13573/262144) | N00858, N00859 |
| N00858 | C01004 | catalogue sharp terminal(4) | C05035 |
| N00859 | C01005 | catalogue sharp terminal(1) | C05036 |
| N00860 | none | positive row contradiction | C01006 |
| N00861 | none | positive row contradiction | C01007 |
| N00862 | C01008 | positive row contradiction | C01009 |
| N00863 | C01010 | angle(8,-13573/131072) | N00864, N00873 |
| N00864 | C01011 | sat(1,7) | N00865, N00866, N00867, N00868, N00869, N00870, N00871, N00872 |
| N00865 | none | positive row contradiction | C01012 |
| N00866 | none | positive row contradiction | C01013 |
| N00867 | C01014 | positive row contradiction | C01015 |
| N00868 | none | positive row contradiction | C01016 |
| N00869 | none | positive row contradiction | C01017 |
| N00870 | none | common-axis chain [[7,0],[1,7,2]] | endpoint squared distance < 4 |
| N00871 | C01018 | positive row contradiction | C01019 |
| N00872 | none | positive row contradiction | C01020 |
| N00873 | C01021 | angle(4,-121/2048) | N00874, N00875 |
| N00874 | C01022 | positive row contradiction | C01023 |
| N00875 | C01024 | angle(8,-13573/262144) | N00876, N00877 |
| N00876 | C01025 | catalogue sharp terminal(4) | C05037 |
| N00877 | C01026 | catalogue sharp terminal(1) | C05038 |
| N00878 | none | positive row contradiction | C01027 |
| N00879 | none | positive row contradiction | C01028 |
| N00880 | C01029 | positive row contradiction | C01030 |
| N00881 | none | positive row contradiction | C01031 |
| N00882 | C01032 | proxy(5,8) | N00883, N00884, N00885, N00886 |
| N00883 | none | positive row contradiction | C01033 |
| N00884 | C01034 | positive row contradiction | C01035 |
| N00885 | C01036 | positive row contradiction | C01037 |
| N00886 | none | positive row contradiction | C01038 |
| N00887 | none | positive row contradiction | C01039 |
| N00888 | C01040 | positive row contradiction | C01041 |
| N00889 | C01042 | proxy(7,8) | N00890, N00891, N00906, N00907 |
| N00890 | none | positive row contradiction | C01043 |
| N00891 | C01044 | angle(8,-13573/65536) | N00892, N00901 |
| N00892 | C01045 | sat(2,8) | N00893, N00894, N00895, N00896, N00897, N00898, N00899, N00900 |
| N00893 | none | positive row contradiction | C01046 |
| N00894 | none | positive row contradiction | C01047 |
| N00895 | none | positive row contradiction | C01048 |
| N00896 | none | positive row contradiction | C01049 |
| N00897 | none | positive row contradiction | C01050 |
| N00898 | none | positive row contradiction | C01051 |
| N00899 | none | positive row contradiction | C01052 |
| N00900 | none | positive row contradiction | C01053 |
| N00901 | C01054 | proxy(2,8) | N00902, N00903, N00904, N00905 |
| N00902 | C01055 | positive row contradiction | C01056 |
| N00903 | none | positive row contradiction | C01057 |
| N00904 | none | positive row contradiction | C01058 |
| N00905 | none | positive row contradiction | C01059 |
| N00906 | C01060 | positive row contradiction | C01061 |
| N00907 | C01062 | positive row contradiction | C01063 |
| N00908 | C01064 | proxy(5,8) | N00909, N00910, N00911, N00956 |
| N00909 | C01065 | positive row contradiction | C01066 |
| N00910 | C01067 | positive row contradiction | C01068 |
| N00911 | C01069 | angle(6,13573/65536) | N00912, N00955 |
| N00912 | C01070 | sat(4,8) | N00913, N00914, N00929, N00930, N00931, N00932, N00953, N00954 |
| N00913 | none | positive row contradiction | C01071 |
| N00914 | C01072 | proxy(6,8) | N00915, N00926, N00927, N00928 |
| N00915 | C01073 | angle(8,-13573/65536) | N00916, N00917 |
| N00916 | C01074 | positive row contradiction | C01075 |
| N00917 | C01076 | sat(2,7) | N00918, N00919, N00920, N00921, N00922, N00923, N00924, N00925 |
| N00918 | C01077 | positive row contradiction | C01078 |
| N00919 | none | positive row contradiction | C01079 |
| N00920 | none | positive row contradiction | C01080 |
| N00921 | none | positive row contradiction | C01081 |
| N00922 | C01082 | positive row contradiction | C01083 |
| N00923 | none | positive row contradiction | C01084 |
| N00924 | none | positive row contradiction | C01085 |
| N00925 | none | positive row contradiction | C01086 |
| N00926 | none | positive row contradiction | C01087 |
| N00927 | none | positive row contradiction | C01088 |
| N00928 | none | positive row contradiction | C01089 |
| N00929 | none | positive row contradiction | C01090 |
| N00930 | C01091 | positive row contradiction | C01092 |
| N00931 | none | positive row contradiction | C01093 |
| N00932 | C01094 | sat(2,7) | N00933, N00944, N00945, N00946, N00947, N00950, N00951, N00952 |
| N00933 | C01095 | angle(7,-13573/65536) | N00934, N00935 |
| N00934 | C01096 | positive row contradiction | C01097 |
| N00935 | C01098 | sat(6,8) | N00936, N00937, N00938, N00939, N00940, N00941, N00942, N00943 |
| N00936 | C01099 | positive row contradiction | C01100 |
| N00937 | none | positive row contradiction | C01101 |
| N00938 | none | positive row contradiction | C01102 |
| N00939 | none | positive row contradiction | C01103 |
| N00940 | C01104 | positive row contradiction | C01105 |
| N00941 | none | positive row contradiction | C01106 |
| N00942 | none | positive row contradiction | C01107 |
| N00943 | none | positive row contradiction | C01108 |
| N00944 | none | positive row contradiction | C01109 |
| N00945 | none | positive row contradiction | C01110 |
| N00946 | none | positive row contradiction | C01111 |
| N00947 | C01112 | angle(8,-6939/32768) | N00948, N00949 |
| N00948 | C01113 | positive row contradiction | C01114 |
| N00949 | C01115 | positive row contradiction | C01116 |
| N00950 | none | positive row contradiction | C01117 |
| N00951 | C01118 | positive row contradiction | C01119 |
| N00952 | none | positive row contradiction | C01120 |
| N00953 | none | positive row contradiction | C01121 |
| N00954 | C01122 | positive row contradiction | C01123 |
| N00955 | C01124 | positive row contradiction | C01125 |
| N00956 | C01126 | angle(4,-13573/65536) | N00957, N00958 |
| N00957 | C01127 | positive row contradiction | C01128 |
| N00958 | C01129 | sat(4,8) | N00959, N00960, N00963, N00964, N00965, N00966, N00971, N00972 |
| N00959 | none | positive row contradiction | C01130 |
| N00960 | C01131 | angle(8,-13573/65536) | N00961, N00962 |
| N00961 | none | positive row contradiction | C01132 |
| N00962 | C01133 | positive row contradiction | C01134 |
| N00963 | none | positive row contradiction | C01135 |
| N00964 | C01136 | positive row contradiction | C01137 |
| N00965 | none | positive row contradiction | C01138 |
| N00966 | C01139 | proxy(6,8) | N00967, N00968, N00969, N00970 |
| N00967 | C01140 | positive row contradiction | C01141 |
| N00968 | none | positive row contradiction | C01142 |
| N00969 | none | positive row contradiction | C01143 |
| N00970 | none | positive row contradiction | C01144 |
| N00971 | none | positive row contradiction | C01145 |
| N00972 | C01146 | angle(8,-4071/16384) | N00973, N00974 |
| N00973 | none | positive row contradiction | C01147 |
| N00974 | none | positive row contradiction | C01148 |
| N00975 | C01149 | angle(5,0) | N00976, N01211 |
| N00976 | C01150 | angle(4,13573/65536) | N00977, N01188 |
| N00977 | C01151 | angle(3,-13573/65536) | N00978, N00979 |
| N00978 | C01152 | positive row contradiction | C01153 |
| N00979 | C01154 | proxy(1,8) | N00980, N00981, N01130, N01141 |
| N00980 | none | positive row contradiction | C01155 |
| N00981 | C01156 | proxy(2,8) | N00982, N00983, N00984, N00985 |
| N00982 | none | positive row contradiction | C01157 |
| N00983 | C01158 | positive row contradiction | C01159 |
| N00984 | none | positive row contradiction | C01160 |
| N00985 | C01161 | angle(7,-13573/65536) | N00986, N01073 |
| N00986 | C01162 | proxy(1,4) | N00987, N00988, N00989, N00990 |
| N00987 | none | positive row contradiction | C01163 |
| N00988 | none | positive row contradiction | C01164 |
| N00989 | none | positive row contradiction | C01165 |
| N00990 | C01166 | sat(2,8) | N00991, N00992, N00993, N00994, N01025, N01026, N01027, N01028 |
| N00991 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N00992 | none | positive row contradiction | C01167 |
| N00993 | none | positive row contradiction | C01168 |
| N00994 | C01169 | proxy(5,8) | N00995, N00996, N00997, N01024 |
| N00995 | none | positive row contradiction | C01170 |
| N00996 | C01171 | positive row contradiction | C01172 |
| N00997 | C01173 | sat(5,8) | N00998, N00999, N01000, N01009, N01010, N01011, N01014, N01023 |
| N00998 | none | positive row contradiction | C01174 |
| N00999 | none | positive row contradiction | C01175 |
| N01000 | C01176 | proxy(6,8) | N01001, N01002, N01003, N01008 |
| N01001 | none | positive row contradiction | C01177 |
| N01002 | none | positive row contradiction | C01178 |
| N01003 | C01179 | angle(8,-25685/131072) | N01004, N01005 |
| N01004 | none | positive row contradiction | C01180 |
| N01005 | C01181 | angle(8,-8151/131072) | N01006, N01007 |
| N01006 | C01182 | positive row contradiction | C01183 |
| N01007 | C01184 | catalogue sharp terminal(1) | C05045 |
| N01008 | none | positive row contradiction | C01185 |
| N01009 | none | positive row contradiction | C01186 |
| N01010 | none | positive row contradiction | C01187 |
| N01011 | C01188 | angle(8,-28461/131072) | N01012, N01013 |
| N01012 | none | positive row contradiction | C01189 |
| N01013 | none | positive row contradiction | C01190 |
| N01014 | C01191 | angle(8,-1289/8192) | N01015, N01016 |
| N01015 | C01192 | positive row contradiction | C01193 |
| N01016 | C01194 | proxy(6,8) | N01017, N01018, N01019, N01022 |
| N01017 | none | positive row contradiction | C01195 |
| N01018 | none | positive row contradiction | C01196 |
| N01019 | C01197 | angle(8,-1289/16384) | N01020, N01021 |
| N01020 | C01198 | positive row contradiction | C01199 |
| N01021 | C01200 | catalogue sharp terminal(3) | C05046 |
| N01022 | none | positive row contradiction | C01201 |
| N01023 | none | positive row contradiction | C01202 |
| N01024 | C01203 | positive row contradiction | C01204 |
| N01025 | C01205 | positive row contradiction | C01206 |
| N01026 | none | positive row contradiction | C01207 |
| N01027 | none | positive row contradiction | C01208 |
| N01028 | C01209 | angle(8,-13573/65536) | N01029, N01034 |
| N01029 | C01210 | proxy(3,8) | N01030, N01031, N01032, N01033 |
| N01030 | C01211 | positive row contradiction | C01212 |
| N01031 | none | positive row contradiction | C01213 |
| N01032 | none | positive row contradiction | C01214 |
| N01033 | none | positive row contradiction | C01215 |
| N01034 | C01216 | proxy(3,8) | N01035, N01070, N01071, N01072 |
| N01035 | C01217 | proxy(5,8) | N01036, N01037, N01038, N01069 |
| N01036 | none | positive row contradiction | C01218 |
| N01037 | none | positive row contradiction | C01219 |
| N01038 | C01220 | sat(1,7) | N01039, N01040, N01041, N01046, N01047, N01048, N01049, N01068 |
| N01039 | none | positive row contradiction | C01221 |
| N01040 | none | positive row contradiction | C01222 |
| N01041 | C01223 | angle(8,-3075/32768) | N01042, N01043 |
| N01042 | C01224 | positive row contradiction | C01225 |
| N01043 | C01226 | angle(8,-3075/65536) | N01044, N01045 |
| N01044 | C01227 | positive row contradiction | C01228 |
| N01045 | C01229 | uniform sharp terminal | C05051 |
| N01046 | none | positive row contradiction | C01230 |
| N01047 | none | positive row contradiction | C01231 |
| N01048 | none | positive row contradiction | C01232 |
| N01049 | C01233 | sat(0,7) | N01050, N01051, N01052, N01061, N01062, N01063, N01066, N01067 |
| N01050 | none | positive row contradiction | C01234 |
| N01051 | none | positive row contradiction | C01235 |
| N01052 | C01236 | sat(6,8) | N01053, N01054, N01055, N01056, N01057, N01058, N01059, N01060 |
| N01053 | none | positive row contradiction | C01237 |
| N01054 | none | positive row contradiction | C01238 |
| N01055 | C01239 | uniform sharp terminal | C05052 |
| N01056 | none | positive row contradiction | C01240 |
| N01057 | none | positive row contradiction | C01241 |
| N01058 | none | positive row contradiction | C01242 |
| N01059 | C01243 | uniform sharp terminal | C05053 |
| N01060 | none | positive row contradiction | C01244 |
| N01061 | none | positive row contradiction | C01245 |
| N01062 | none | positive row contradiction | C01246 |
| N01063 | C01247 | angle(8,-7349/131072) | N01064, N01065 |
| N01064 | C01248 | positive row contradiction | C01249 |
| N01065 | C01250 | catalogue sharp terminal(1) | C05054 |
| N01066 | none | positive row contradiction | C01251 |
| N01067 | none | common-axis chain [[7,1],[0,7,1]] | endpoint squared distance < 4 |
| N01068 | none | positive row contradiction | C01252 |
| N01069 | none | positive row contradiction | C01253 |
| N01070 | none | positive row contradiction | C01254 |
| N01071 | none | positive row contradiction | C01255 |
| N01072 | C01256 | positive row contradiction | C01257 |
| N01073 | C01258 | angle(6,6235/32768) | N01074, N01129 |
| N01074 | C01259 | proxy(1,4) | N01075, N01076, N01077, N01078 |
| N01075 | none | positive row contradiction | C01260 |
| N01076 | none | positive row contradiction | C01261 |
| N01077 | none | positive row contradiction | C01262 |
| N01078 | C01263 | proxy(5,8) | N01079, N01080, N01085, N01128 |
| N01079 | none | positive row contradiction | C01264 |
| N01080 | C01265 | proxy(3,8) | N01081, N01082, N01083, N01084 |
| N01081 | none | positive row contradiction | C01266 |
| N01082 | none | positive row contradiction | C01267 |
| N01083 | none | positive row contradiction | C01268 |
| N01084 | none | positive row contradiction | C01269 |
| N01085 | C01270 | sat(5,8) | N01086, N01087, N01088, N01105, N01106, N01107, N01110, N01127 |
| N01086 | none | positive row contradiction | C01271 |
| N01087 | none | positive row contradiction | C01272 |
| N01088 | C01273 | angle(8,-13573/65536) | N01089, N01090 |
| N01089 | C01274 | positive row contradiction | C01275 |
| N01090 | C01276 | angle(8,-13573/131072) | N01091, N01100 |
| N01091 | C01277 | sat(1,8) | N01092, N01093, N01094, N01095, N01096, N01097, N01098, N01099 |
| N01092 | none | positive row contradiction | C01278 |
| N01093 | none | positive row contradiction | C01279 |
| N01094 | none | positive row contradiction | C01280 |
| N01095 | none | positive row contradiction | C01281 |
| N01096 | none | positive row contradiction | C01282 |
| N01097 | none | positive row contradiction | C01283 |
| N01098 | none | positive row contradiction | C01284 |
| N01099 | none | positive row contradiction | C01285 |
| N01100 | C01286 | angle(8,-13573/262144) | N01101, N01104 |
| N01101 | C01287 | angle(8,-40719/524288) | N01102, N01103 |
| N01102 | C01288 | positive row contradiction | C01289 |
| N01103 | C01290 | catalogue sharp terminal(3) | C05055 |
| N01104 | C01291 | catalogue sharp terminal(1) | C05047 |
| N01105 | none | positive row contradiction | C01292 |
| N01106 | none | positive row contradiction | C01293 |
| N01107 | C01294 | angle(8,-27207/131072) | N01108, N01109 |
| N01108 | C01295 | positive row contradiction | C01296 |
| N01109 | none | positive row contradiction | C01297 |
| N01110 | C01298 | sat(1,8) | N01111, N01112, N01117, N01118, N01119, N01120, N01125, N01126 |
| N01111 | none | positive row contradiction | C01299 |
| N01112 | C01300 | angle(8,-11995/131072) | N01113, N01114 |
| N01113 | none | positive row contradiction | C01301 |
| N01114 | C01302 | angle(8,-2325/65536) | N01115, N01116 |
| N01115 | C01303 | positive row contradiction | C01304 |
| N01116 | C01305 | uniform sharp terminal | C05048 |
| N01117 | none | positive row contradiction | C01306 |
| N01118 | none | positive row contradiction | C01307 |
| N01119 | none | positive row contradiction | C01308 |
| N01120 | C01309 | angle(8,-12585/131072) | N01121, N01122 |
| N01121 | none | positive row contradiction | C01310 |
| N01122 | C01311 | angle(8,-5167/131072) | N01123, N01124 |
| N01123 | none | positive row contradiction | C01312 |
| N01124 | C01313 | uniform sharp terminal | C05049 |
| N01125 | none | positive row contradiction | C01314 |
| N01126 | C01315 | positive row contradiction | C01316 |
| N01127 | none | positive row contradiction | C01317 |
| N01128 | C01318 | positive row contradiction | C01319 |
| N01129 | none | positive row contradiction | C01320 |
| N01130 | C01321 | angle(6,13573/65536) | N01131, N01140 |
| N01131 | C01322 | proxy(7,8) | N01132, N01133, N01138, N01139 |
| N01132 | none | positive row contradiction | C01323 |
| N01133 | C01324 | proxy(2,8) | N01134, N01135, N01136, N01137 |
| N01134 | C01325 | positive row contradiction | C01326 |
| N01135 | none | positive row contradiction | C01327 |
| N01136 | none | positive row contradiction | C01328 |
| N01137 | none | positive row contradiction | C01329 |
| N01138 | none | positive row contradiction | C01330 |
| N01139 | none | positive row contradiction | C01331 |
| N01140 | C01332 | positive row contradiction | C01333 |
| N01141 | C01334 | proxy(5,8) | N01142, N01143, N01144, N01175 |
| N01142 | C01335 | positive row contradiction | C01336 |
| N01143 | C01337 | positive row contradiction | C01338 |
| N01144 | C01339 | angle(7,-13573/65536) | N01145, N01158 |
| N01145 | C01340 | proxy(4,8) | N01146, N01147, N01156, N01157 |
| N01146 | none | positive row contradiction | C01341 |
| N01147 | C01342 | sat(4,8) | N01148, N01149, N01150, N01151, N01152, N01153, N01154, N01155 |
| N01148 | none | positive row contradiction | C01343 |
| N01149 | C01344 | positive row contradiction | C01345 |
| N01150 | none | positive row contradiction | C01346 |
| N01151 | none | positive row contradiction | C01347 |
| N01152 | none | positive row contradiction | C01348 |
| N01153 | C01349 | positive row contradiction | C01350 |
| N01154 | none | positive row contradiction | C01351 |
| N01155 | none | positive row contradiction | C01352 |
| N01156 | none | positive row contradiction | C01353 |
| N01157 | none | positive row contradiction | C01354 |
| N01158 | C01355 | angle(6,6235/32768) | N01159, N01174 |
| N01159 | C01356 | sat(1,8) | N01160, N01161, N01162, N01163, N01164, N01165, N01166, N01167 |
| N01160 | none | positive row contradiction | C01357 |
| N01161 | C01358 | positive row contradiction | C01359 |
| N01162 | none | positive row contradiction | C01360 |
| N01163 | C01361 | positive row contradiction | C01362 |
| N01164 | none | positive row contradiction | C01363 |
| N01165 | C01364 | positive row contradiction | C01365 |
| N01166 | none | positive row contradiction | C01366 |
| N01167 | C01367 | proxy(6,8) | N01168, N01171, N01172, N01173 |
| N01168 | C01368 | angle(8,-13573/65536) | N01169, N01170 |
| N01169 | none | positive row contradiction | C01369 |
| N01170 | C01370 | positive row contradiction | C01371 |
| N01171 | none | positive row contradiction | C01372 |
| N01172 | none | positive row contradiction | C01373 |
| N01173 | none | positive row contradiction | C01374 |
| N01174 | none | positive row contradiction | C01375 |
| N01175 | C01376 | proxy(4,8) | N01176, N01177, N01186, N01187 |
| N01176 | none | positive row contradiction | C01377 |
| N01177 | C01378 | sat(2,7) | N01178, N01179, N01180, N01181, N01182, N01183, N01184, N01185 |
| N01178 | C01379 | positive row contradiction | C01380 |
| N01179 | none | positive row contradiction | C01381 |
| N01180 | none | positive row contradiction | C01382 |
| N01181 | none | positive row contradiction | C01383 |
| N01182 | C01384 | positive row contradiction | C01385 |
| N01183 | none | positive row contradiction | C01386 |
| N01184 | none | positive row contradiction | C01387 |
| N01185 | none | positive row contradiction | C01388 |
| N01186 | none | positive row contradiction | C01389 |
| N01187 | none | positive row contradiction | C01390 |
| N01188 | C01391 | angle(3,-13573/65536) | N01189, N01190 |
| N01189 | C01392 | positive row contradiction | C01393 |
| N01190 | C01394 | angle(6,13573/65536) | N01191, N01210 |
| N01191 | C01395 | proxy(1,8) | N01192, N01193, N01202, N01205 |
| N01192 | none | positive row contradiction | C01396 |
| N01193 | C01397 | sat(5,8) | N01194, N01195, N01196, N01197, N01198, N01199, N01200, N01201 |
| N01194 | none | positive row contradiction | C01398 |
| N01195 | C01399 | positive row contradiction | C01400 |
| N01196 | C01401 | positive row contradiction | C01402 |
| N01197 | none | positive row contradiction | C01403 |
| N01198 | none | positive row contradiction | C01404 |
| N01199 | C01405 | positive row contradiction | C01406 |
| N01200 | C01407 | positive row contradiction | C01408 |
| N01201 | C01409 | positive row contradiction | C01410 |
| N01202 | C01411 | angle(7,-13573/65536) | N01203, N01204 |
| N01203 | C01412 | positive row contradiction | C01413 |
| N01204 | C01414 | positive row contradiction | C01415 |
| N01205 | C01416 | proxy(4,8) | N01206, N01207, N01208, N01209 |
| N01206 | none | positive row contradiction | C01417 |
| N01207 | C01418 | positive row contradiction | C01419 |
| N01208 | C01420 | positive row contradiction | C01421 |
| N01209 | none | positive row contradiction | C01422 |
| N01210 | C01423 | positive row contradiction | C01424 |
| N01211 | C01425 | angle(3,-13573/65536) | N01212, N01213 |
| N01212 | C01426 | positive row contradiction | C01427 |
| N01213 | C01428 | angle(2,20839/131072) | N01214, N01605 |
| N01214 | C01429 | proxy(7,8) | N01215, N01216, N01507, N01508 |
| N01215 | none | positive row contradiction | C01430 |
| N01216 | C01431 | sat(1,7) | N01217, N01218, N01219, N01362, N01363, N01364, N01365, N01506 |
| N01217 | none | positive row contradiction | C01432 |
| N01218 | none | positive row contradiction | C01433 |
| N01219 | C01434 | angle(8,-13573/65536) | N01220, N01291 |
| N01220 | C01435 | sat(5,8) | N01221, N01222, N01227, N01244, N01245, N01246, N01271, N01290 |
| N01221 | none | positive row contradiction | C01436 |
| N01222 | C01437 | proxy(3,8) | N01223, N01224, N01225, N01226 |
| N01223 | none | positive row contradiction | C01438 |
| N01224 | none | positive row contradiction | C01439 |
| N01225 | none | positive row contradiction | C01440 |
| N01226 | none | positive row contradiction | C01441 |
| N01227 | C01442 | proxy(1,8) | N01228, N01229, N01242, N01243 |
| N01228 | none | positive row contradiction | C01443 |
| N01229 | C01444 | proxy(6,8) | N01230, N01231, N01232, N01241 |
| N01230 | none | positive row contradiction | C01445 |
| N01231 | none | positive row contradiction | C01446 |
| N01232 | C01447 | sat(1,8) | N01233, N01234, N01235, N01236, N01237, N01238, N01239, N01240 |
| N01233 | none | positive row contradiction | C01448 |
| N01234 | none | positive row contradiction | C01449 |
| N01235 | none | positive row contradiction | C01450 |
| N01236 | none | positive row contradiction | C01451 |
| N01237 | none | positive row contradiction | C01452 |
| N01238 | none | positive row contradiction | C01453 |
| N01239 | none | positive row contradiction | C01454 |
| N01240 | none | positive row contradiction | C01455 |
| N01241 | none | positive row contradiction | C01456 |
| N01242 | C01457 | positive row contradiction | C01458 |
| N01243 | none | positive row contradiction | C01459 |
| N01244 | none | positive row contradiction | C01460 |
| N01245 | none | positive row contradiction | C01461 |
| N01246 | C01462 | angle(7,-13573/65536) | N01247, N01258 |
| N01247 | C01463 | proxy(1,8) | N01248, N01249, N01256, N01257 |
| N01248 | none | positive row contradiction | C01464 |
| N01249 | C01465 | proxy(2,8) | N01250, N01251, N01252, N01253 |
| N01250 | none | positive row contradiction | C01466 |
| N01251 | none | positive row contradiction | C01467 |
| N01252 | none | positive row contradiction | C01468 |
| N01253 | C01469 | angle(8,-40719/131072) | N01254, N01255 |
| N01254 | C01470 | positive row contradiction | C01471 |
| N01255 | C01472 | positive row contradiction | C01473 |
| N01256 | C01474 | positive row contradiction | C01475 |
| N01257 | C01476 | positive row contradiction | C01477 |
| N01258 | C01478 | proxy(6,8) | N01259, N01262, N01263, N01270 |
| N01259 | C01479 | angle(8,-40719/131072) | N01260, N01261 |
| N01260 | C01480 | positive row contradiction | C01481 |
| N01261 | C01482 | positive row contradiction | C01483 |
| N01262 | none | positive row contradiction | C01484 |
| N01263 | C01485 | proxy(2,8) | N01264, N01265, N01266, N01267 |
| N01264 | none | positive row contradiction | C01486 |
| N01265 | none | positive row contradiction | C01487 |
| N01266 | none | positive row contradiction | C01488 |
| N01267 | C01489 | angle(8,-40719/131072) | N01268, N01269 |
| N01268 | C01490 | positive row contradiction | C01491 |
| N01269 | C01492 | positive row contradiction | C01493 |
| N01270 | none | positive row contradiction | C01494 |
| N01271 | C01495 | angle(7,-13573/65536) | N01272, N01281 |
| N01272 | C01496 | proxy(2,8) | N01273, N01274, N01275, N01276 |
| N01273 | C01497 | positive row contradiction | C01498 |
| N01274 | none | positive row contradiction | C01499 |
| N01275 | none | positive row contradiction | C01500 |
| N01276 | C01501 | proxy(1,8) | N01277, N01278, N01279, N01280 |
| N01277 | none | positive row contradiction | C01502 |
| N01278 | C01503 | positive row contradiction | C01504 |
| N01279 | none | positive row contradiction | C01505 |
| N01280 | none | positive row contradiction | C01506 |
| N01281 | C01507 | proxy(2,8) | N01282, N01283, N01284, N01285 |
| N01282 | none | positive row contradiction | C01508 |
| N01283 | none | positive row contradiction | C01509 |
| N01284 | none | positive row contradiction | C01510 |
| N01285 | C01511 | proxy(1,8) | N01286, N01287, N01288, N01289 |
| N01286 | none | positive row contradiction | C01512 |
| N01287 | C01513 | positive row contradiction | C01514 |
| N01288 | none | positive row contradiction | C01515 |
| N01289 | none | positive row contradiction | C01516 |
| N01290 | C01517 | positive row contradiction | C01518 |
| N01291 | C01519 | sat(6,8) | N01292, N01311, N01312, N01335, N01336, N01347, N01348, N01361 |
| N01292 | C01520 | angle(7,-13573/65536) | N01293, N01302 |
| N01293 | C01521 | proxy(5,8) | N01294, N01295, N01296, N01301 |
| N01294 | none | positive row contradiction | C01522 |
| N01295 | none | positive row contradiction | C01523 |
| N01296 | C01524 | proxy(1,8) | N01297, N01298, N01299, N01300 |
| N01297 | none | positive row contradiction | C01525 |
| N01298 | none | positive row contradiction | C01526 |
| N01299 | C01527 | positive row contradiction | C01528 |
| N01300 | none | positive row contradiction | C01529 |
| N01301 | none | positive row contradiction | C01530 |
| N01302 | C01531 | proxy(5,8) | N01303, N01304, N01305, N01310 |
| N01303 | none | positive row contradiction | C01532 |
| N01304 | none | positive row contradiction | C01533 |
| N01305 | C01534 | proxy(1,8) | N01306, N01307, N01308, N01309 |
| N01306 | none | positive row contradiction | C01535 |
| N01307 | none | positive row contradiction | C01536 |
| N01308 | C01537 | positive row contradiction | C01538 |
| N01309 | none | positive row contradiction | C01539 |
| N01310 | none | positive row contradiction | C01540 |
| N01311 | none | positive row contradiction | C01541 |
| N01312 | C01542 | angle(7,-13573/65536) | N01313, N01326 |
| N01313 | C01543 | angle(8,-13573/131072) | N01314, N01319 |
| N01314 | C01544 | proxy(1,8) | N01315, N01316, N01317, N01318 |
| N01315 | none | positive row contradiction | C01545 |
| N01316 | C01546 | positive row contradiction | C01547 |
| N01317 | none | positive row contradiction | C01548 |
| N01318 | none | positive row contradiction | C01549 |
| N01319 | C01550 | proxy(1,8) | N01320, N01321, N01324, N01325 |
| N01320 | none | positive row contradiction | C01551 |
| N01321 | C01552 | angle(8,-13573/262144) | N01322, N01323 |
| N01322 | C01553 | positive row contradiction | C01554 |
| N01323 | C01555 | catalogue sharp terminal(1) | C05020 |
| N01324 | none | positive row contradiction | C01556 |
| N01325 | none | positive row contradiction | C01557 |
| N01326 | C01558 | proxy(1,8) | N01327, N01328, N01333, N01334 |
| N01327 | none | positive row contradiction | C01559 |
| N01328 | C01560 | angle(8,-13573/131072) | N01329, N01330 |
| N01329 | C01561 | positive row contradiction | C01562 |
| N01330 | C01563 | angle(8,-13573/262144) | N01331, N01332 |
| N01331 | C01564 | positive row contradiction | C01565 |
| N01332 | C01566 | catalogue sharp terminal(1) | C05021 |
| N01333 | none | positive row contradiction | C01567 |
| N01334 | none | positive row contradiction | C01568 |
| N01335 | none | positive row contradiction | C01569 |
| N01336 | C01570 | proxy(5,8) | N01337, N01338, N01339, N01346 |
| N01337 | none | positive row contradiction | C01571 |
| N01338 | none | positive row contradiction | C01572 |
| N01339 | C01573 | angle(7,-13573/65536) | N01340, N01345 |
| N01340 | C01574 | proxy(2,8) | N01341, N01342, N01343, N01344 |
| N01341 | none | positive row contradiction | C01575 |
| N01342 | none | positive row contradiction | C01576 |
| N01343 | none | positive row contradiction | C01577 |
| N01344 | C01578 | positive row contradiction | C01579 |
| N01345 | C01580 | positive row contradiction | C01581 |
| N01346 | none | positive row contradiction | C01582 |
| N01347 | none | positive row contradiction | C01583 |
| N01348 | C01584 | proxy(2,8) | N01349, N01350, N01351, N01352 |
| N01349 | none | positive row contradiction | C01585 |
| N01350 | none | positive row contradiction | C01586 |
| N01351 | none | positive row contradiction | C01587 |
| N01352 | C01588 | proxy(1,8) | N01353, N01354, N01359, N01360 |
| N01353 | none | positive row contradiction | C01589 |
| N01354 | C01590 | angle(8,-13573/131072) | N01355, N01356 |
| N01355 | C01591 | positive row contradiction | C01592 |
| N01356 | C01593 | angle(8,-13573/262144) | N01357, N01358 |
| N01357 | C01594 | positive row contradiction | C01595 |
| N01358 | C01596 | catalogue sharp terminal(1) | C05022 |
| N01359 | none | positive row contradiction | C01597 |
| N01360 | none | positive row contradiction | C01598 |
| N01361 | none | positive row contradiction | C01599 |
| N01362 | none | positive row contradiction | C01600 |
| N01363 | none | positive row contradiction | C01601 |
| N01364 | none | positive row contradiction | C01602 |
| N01365 | C01603 | proxy(1,8) | N01366, N01367, N01478, N01481 |
| N01366 | none | positive row contradiction | C01604 |
| N01367 | C01605 | angle(7,-13545/65536) | N01368, N01401 |
| N01368 | C01606 | sat(6,8) | N01369, N01370, N01371, N01380, N01381, N01382, N01383, N01400 |
| N01369 | none | positive row contradiction | C01607 |
| N01370 | none | positive row contradiction | C01608 |
| N01371 | C01609 | proxy(2,8) | N01372, N01373, N01374, N01375 |
| N01372 | none | positive row contradiction | C01610 |
| N01373 | none | positive row contradiction | C01611 |
| N01374 | none | positive row contradiction | C01612 |
| N01375 | C01613 | angle(8,-10695/65536) | N01376, N01377 |
| N01376 | none | positive row contradiction | C01614 |
| N01377 | C01615 | angle(4,1415/32768) | N01378, N01379 |
| N01378 | C01616 | uniform sharp terminal | C05023 |
| N01379 | none | positive row contradiction | C01617 |
| N01380 | none | positive row contradiction | C01618 |
| N01381 | none | positive row contradiction | C01619 |
| N01382 | C01620 | positive row contradiction | C01621 |
| N01383 | C01622 | proxy(2,8) | N01384, N01385, N01386, N01387 |
| N01384 | none | positive row contradiction | C01623 |
| N01385 | none | positive row contradiction | C01624 |
| N01386 | none | positive row contradiction | C01625 |
| N01387 | C01626 | sat(2,8) | N01388, N01389, N01390, N01391, N01394, N01395, N01396, N01397 |
| N01388 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N01389 | none | positive row contradiction | C01627 |
| N01390 | none | positive row contradiction | C01628 |
| N01391 | C01629 | angle(8,-20141/131072) | N01392, N01393 |
| N01392 | none | positive row contradiction | C01630 |
| N01393 | C01631 | catalogue sharp terminal(1) | C05024 |
| N01394 | none | positive row contradiction | C01632 |
| N01395 | none | positive row contradiction | C01633 |
| N01396 | none | positive row contradiction | C01634 |
| N01397 | C01635 | angle(8,-8071/65536) | N01398, N01399 |
| N01398 | none | positive row contradiction | C01636 |
| N01399 | C01637 | catalogue sharp terminal(3) | C05025 |
| N01400 | none | positive row contradiction | C01638 |
| N01401 | C01639 | proxy(5,8) | N01402, N01403, N01408, N01477 |
| N01402 | none | positive row contradiction | C01640 |
| N01403 | C01641 | proxy(6,8) | N01404, N01405, N01406, N01407 |
| N01404 | none | positive row contradiction | C01642 |
| N01405 | none | positive row contradiction | C01643 |
| N01406 | C01644 | positive row contradiction | C01645 |
| N01407 | none | positive row contradiction | C01646 |
| N01408 | C01647 | sat(5,8) | N01409, N01410, N01411, N01432, N01433, N01434, N01453, N01476 |
| N01409 | none | positive row contradiction | C01648 |
| N01410 | C01649 | positive row contradiction | C01650 |
| N01411 | C01651 | proxy(6,8) | N01412, N01413, N01414, N01431 |
| N01412 | none | positive row contradiction | C01652 |
| N01413 | none | positive row contradiction | C01653 |
| N01414 | C01654 | angle(8,-13573/65536) | N01415, N01416 |
| N01415 | C01655 | positive row contradiction | C01656 |
| N01416 | C01657 | angle(8,-13573/131072) | N01417, N01426 |
| N01417 | C01658 | sat(1,8) | N01418, N01419, N01420, N01421, N01422, N01423, N01424, N01425 |
| N01418 | none | positive row contradiction | C01659 |
| N01419 | none | positive row contradiction | C01660 |
| N01420 | none | positive row contradiction | C01661 |
| N01421 | none | positive row contradiction | C01662 |
| N01422 | none | positive row contradiction | C01663 |
| N01423 | none | positive row contradiction | C01664 |
| N01424 | none | positive row contradiction | C01665 |
| N01425 | none | positive row contradiction | C01666 |
| N01426 | C01667 | angle(8,-13573/262144) | N01427, N01430 |
| N01427 | C01668 | angle(8,-40719/524288) | N01428, N01429 |
| N01428 | none | positive row contradiction | C01669 |
| N01429 | C01670 | positive row contradiction | C01671 |
| N01430 | C01672 | catalogue sharp terminal(1) | C05050 |
| N01431 | none | positive row contradiction | C01673 |
| N01432 | none | positive row contradiction | C01674 |
| N01433 | none | positive row contradiction | C01675 |
| N01434 | C01676 | angle(8,-13573/65536) | N01435, N01444 |
| N01435 | C01677 | sat(6,8) | N01436, N01437, N01438, N01439, N01440, N01441, N01442, N01443 |
| N01436 | none | positive row contradiction | C01678 |
| N01437 | none | positive row contradiction | C01679 |
| N01438 | none | positive row contradiction | C01680 |
| N01439 | none | positive row contradiction | C01681 |
| N01440 | none | common-axis chain [[8,0],[5,8,6]] | endpoint squared distance < 4 |
| N01441 | none | positive row contradiction | C01682 |
| N01442 | C01683 | positive row contradiction | C01684 |
| N01443 | none | positive row contradiction | C01685 |
| N01444 | C01686 | proxy(6,8) | N01445, N01446, N01447, N01452 |
| N01445 | none | positive row contradiction | C01687 |
| N01446 | none | positive row contradiction | C01688 |
| N01447 | C01689 | proxy(1,4) | N01448, N01449, N01450, N01451 |
| N01448 | none | positive row contradiction | C01690 |
| N01449 | none | positive row contradiction | C01691 |
| N01450 | none | positive row contradiction | C01692 |
| N01451 | C01693 | positive row contradiction | C01694 |
| N01452 | none | positive row contradiction | C01695 |
| N01453 | C01696 | proxy(6,8) | N01454, N01455, N01456, N01475 |
| N01454 | none | positive row contradiction | C01697 |
| N01455 | none | positive row contradiction | C01698 |
| N01456 | C01699 | angle(8,-26329/131072) | N01457, N01458 |
| N01457 | C01700 | positive row contradiction | C01701 |
| N01458 | C01702 | angle(8,-26329/262144) | N01459, N01468 |
| N01459 | C01703 | sat(1,8) | N01460, N01461, N01462, N01463, N01464, N01465, N01466, N01467 |
| N01460 | none | positive row contradiction | C01704 |
| N01461 | none | positive row contradiction | C01705 |
| N01462 | none | positive row contradiction | C01706 |
| N01463 | none | positive row contradiction | C01707 |
| N01464 | none | positive row contradiction | C01708 |
| N01465 | none | positive row contradiction | C01709 |
| N01466 | none | positive row contradiction | C01710 |
| N01467 | none | common-axis chain [[8,1],[1,8,5]] | endpoint squared distance < 4 |
| N01468 | C01711 | proxy(1,4) | N01469, N01470, N01471, N01472 |
| N01469 | none | positive row contradiction | C01712 |
| N01470 | none | positive row contradiction | C01713 |
| N01471 | none | positive row contradiction | C01714 |
| N01472 | C01715 | angle(8,-26329/524288) | N01473, N01474 |
| N01473 | C01716 | positive row contradiction | C01717 |
| N01474 | C01718 | catalogue sharp terminal(1) | C05056 |
| N01475 | none | positive row contradiction | C01719 |
| N01476 | none | positive row contradiction | C01720 |
| N01477 | none | positive row contradiction | C01721 |
| N01478 | C01722 | angle(7,-13545/65536) | N01479, N01480 |
| N01479 | C01723 | positive row contradiction | C01724 |
| N01480 | C01725 | positive row contradiction | C01726 |
| N01481 | C01727 | angle(8,-13573/65536) | N01482, N01493 |
| N01482 | C01728 | angle(7,-26703/131072) | N01483, N01484 |
| N01483 | C01729 | positive row contradiction | C01730 |
| N01484 | C01731 | sat(6,8) | N01485, N01486, N01487, N01488, N01489, N01490, N01491, N01492 |
| N01485 | none | positive row contradiction | C01732 |
| N01486 | none | positive row contradiction | C01733 |
| N01487 | none | positive row contradiction | C01734 |
| N01488 | none | positive row contradiction | C01735 |
| N01489 | none | positive row contradiction | C01736 |
| N01490 | none | positive row contradiction | C01737 |
| N01491 | none | positive row contradiction | C01738 |
| N01492 | none | positive row contradiction | C01739 |
| N01493 | C01740 | proxy(5,8) | N01494, N01495, N01496, N01505 |
| N01494 | none | positive row contradiction | C01741 |
| N01495 | none | positive row contradiction | C01742 |
| N01496 | C01743 | sat(6,8) | N01497, N01498, N01499, N01500, N01501, N01502, N01503, N01504 |
| N01497 | none | positive row contradiction | C01744 |
| N01498 | none | positive row contradiction | C01745 |
| N01499 | none | positive row contradiction | C01746 |
| N01500 | none | positive row contradiction | C01747 |
| N01501 | none | positive row contradiction | C01748 |
| N01502 | none | positive row contradiction | C01749 |
| N01503 | none | positive row contradiction | C01750 |
| N01504 | none | positive row contradiction | C01751 |
| N01505 | C01752 | positive row contradiction | C01753 |
| N01506 | none | positive row contradiction | C01754 |
| N01507 | none | positive row contradiction | C01755 |
| N01508 | C01756 | proxy(1,8) | N01509, N01510, N01581, N01582 |
| N01509 | none | positive row contradiction | C01757 |
| N01510 | C01758 | sat(1,8) | N01511, N01512, N01541, N01542, N01547, N01548, N01559, N01560 |
| N01511 | none | positive row contradiction | C01759 |
| N01512 | C01760 | proxy(2,8) | N01513, N01514, N01515, N01516 |
| N01513 | none | positive row contradiction | C01761 |
| N01514 | none | positive row contradiction | C01762 |
| N01515 | none | positive row contradiction | C01763 |
| N01516 | C01764 | angle(7,-13573/65536) | N01517, N01530 |
| N01517 | C01765 | angle(8,-13573/65536) | N01518, N01519 |
| N01518 | C01766 | positive row contradiction | C01767 |
| N01519 | C01768 | proxy(5,8) | N01520, N01521, N01522, N01529 |
| N01520 | none | positive row contradiction | C01769 |
| N01521 | none | positive row contradiction | C01770 |
| N01522 | C01771 | proxy(6,8) | N01523, N01524, N01525, N01528 |
| N01523 | none | positive row contradiction | C01772 |
| N01524 | none | positive row contradiction | C01773 |
| N01525 | C01774 | angle(8,-1325/32768) | N01526, N01527 |
| N01526 | none | positive row contradiction | C01775 |
| N01527 | C01776 | uniform sharp terminal | C05039 |
| N01528 | none | positive row contradiction | C01777 |
| N01529 | none | positive row contradiction | C01778 |
| N01530 | C01779 | angle(8,-13573/65536) | N01531, N01532 |
| N01531 | C01780 | positive row contradiction | C01781 |
| N01532 | C01782 | proxy(5,8) | N01533, N01534, N01535, N01540 |
| N01533 | none | positive row contradiction | C01783 |
| N01534 | none | positive row contradiction | C01784 |
| N01535 | C01785 | angle(8,-2761/32768) | N01536, N01537 |
| N01536 | none | positive row contradiction | C01786 |
| N01537 | C01787 | angle(8,-5327/131072) | N01538, N01539 |
| N01538 | C01788 | positive row contradiction | C01789 |
| N01539 | C01790 | uniform sharp terminal | C05040 |
| N01540 | none | positive row contradiction | C01791 |
| N01541 | none | positive row contradiction | C01792 |
| N01542 | C01793 | proxy(5,8) | N01543, N01544, N01545, N01546 |
| N01543 | none | positive row contradiction | C01794 |
| N01544 | none | positive row contradiction | C01795 |
| N01545 | none | positive row contradiction | C01796 |
| N01546 | C01797 | positive row contradiction | C01798 |
| N01547 | none | positive row contradiction | C01799 |
| N01548 | C01800 | proxy(6,8) | N01549, N01550, N01551, N01558 |
| N01549 | none | positive row contradiction | C01801 |
| N01550 | none | positive row contradiction | C01802 |
| N01551 | C01803 | angle(8,-13573/65536) | N01552, N01553 |
| N01552 | none | positive row contradiction | C01804 |
| N01553 | C01805 | angle(8,-13241/131072) | N01554, N01555 |
| N01554 | none | positive row contradiction | C01806 |
| N01555 | C01807 | angle(4,3505/65536) | N01556, N01557 |
| N01556 | C01808 | catalogue sharp terminal(2) | C05019 |
| N01557 | C01809 | positive row contradiction | C01810 |
| N01558 | none | positive row contradiction | C01811 |
| N01559 | none | positive row contradiction | C01812 |
| N01560 | C01813 | angle(7,-13573/65536) | N01561, N01570 |
| N01561 | C01814 | proxy(5,8) | N01562, N01563, N01566, N01569 |
| N01562 | none | positive row contradiction | C01815 |
| N01563 | C01816 | angle(8,-13573/65536) | N01564, N01565 |
| N01564 | none | positive row contradiction | C01817 |
| N01565 | C01818 | positive row contradiction | C01819 |
| N01566 | C01820 | angle(8,-27317/131072) | N01567, N01568 |
| N01567 | C01821 | positive row contradiction | C01822 |
| N01568 | none | positive row contradiction | C01823 |
| N01569 | none | positive row contradiction | C01824 |
| N01570 | C01825 | proxy(5,8) | N01571, N01572, N01577, N01580 |
| N01571 | none | positive row contradiction | C01826 |
| N01572 | C01827 | proxy(6,8) | N01573, N01574, N01575, N01576 |
| N01573 | none | positive row contradiction | C01828 |
| N01574 | none | positive row contradiction | C01829 |
| N01575 | none | positive row contradiction | C01830 |
| N01576 | none | positive row contradiction | C01831 |
| N01577 | C01832 | angle(8,-13573/65536) | N01578, N01579 |
| N01578 | C01833 | positive row contradiction | C01834 |
| N01579 | C01835 | positive row contradiction | C01836 |
| N01580 | C01837 | positive row contradiction | C01838 |
| N01581 | none | positive row contradiction | C01839 |
| N01582 | C01840 | proxy(6,8) | N01583, N01602, N01603, N01604 |
| N01583 | C01841 | proxy(5,8) | N01584, N01585, N01586, N01599 |
| N01584 | C01842 | positive row contradiction | C01843 |
| N01585 | none | positive row contradiction | C01844 |
| N01586 | C01845 | angle(8,-13573/65536) | N01587, N01590 |
| N01587 | C01846 | angle(7,-13573/65536) | N01588, N01589 |
| N01588 | none | positive row contradiction | C01847 |
| N01589 | C01848 | positive row contradiction | C01849 |
| N01590 | C01850 | sat(5,8) | N01591, N01592, N01593, N01594, N01595, N01596, N01597, N01598 |
| N01591 | none | positive row contradiction | C01851 |
| N01592 | none | positive row contradiction | C01852 |
| N01593 | C01853 | positive row contradiction | C01854 |
| N01594 | none | positive row contradiction | C01855 |
| N01595 | none | positive row contradiction | C01856 |
| N01596 | none | positive row contradiction | C01857 |
| N01597 | C01858 | positive row contradiction | C01859 |
| N01598 | none | positive row contradiction | C01860 |
| N01599 | C01861 | angle(7,-13573/65536) | N01600, N01601 |
| N01600 | none | positive row contradiction | C01862 |
| N01601 | C01863 | positive row contradiction | C01864 |
| N01602 | none | positive row contradiction | C01865 |
| N01603 | none | positive row contradiction | C01866 |
| N01604 | none | positive row contradiction | C01867 |
| N01605 | C01868 | positive row contradiction | C01869 |
| N01606 | C01870 | angle(6,0) | N01607, N02120 |
| N01607 | C01871 | angle(4,0) | N01608, N01871 |
| N01608 | C01872 | angle(5,0) | N01609, N01698 |
| N01609 | C01873 | angle(2,13573/65536) | N01610, N01695 |
| N01610 | C01874 | proxy(1,8) | N01611, N01612, N01647, N01656 |
| N01611 | none | positive row contradiction | C01875 |
| N01612 | C01876 | proxy(5,8) | N01613, N01614, N01623, N01646 |
| N01613 | none | positive row contradiction | C01877 |
| N01614 | C01878 | proxy(2,8) | N01615, N01616, N01617, N01618 |
| N01615 | none | positive row contradiction | C01879 |
| N01616 | none | positive row contradiction | C01880 |
| N01617 | none | positive row contradiction | C01881 |
| N01618 | C01882 | proxy(6,8) | N01619, N01620, N01621, N01622 |
| N01619 | none | positive row contradiction | C01883 |
| N01620 | none | positive row contradiction | C01884 |
| N01621 | none | positive row contradiction | C01885 |
| N01622 | none | positive row contradiction | C01886 |
| N01623 | C01887 | proxy(2,8) | N01624, N01625, N01626, N01627 |
| N01624 | none | positive row contradiction | C01888 |
| N01625 | none | positive row contradiction | C01889 |
| N01626 | none | positive row contradiction | C01890 |
| N01627 | C01891 | angle(8,13573/65536) | N01628, N01643 |
| N01628 | C01892 | angle(4,-1379/8192) | N01629, N01630 |
| N01629 | none | positive row contradiction | C01893 |
| N01630 | C01894 | angle(8,13573/131072) | N01631, N01640 |
| N01631 | C01895 | proxy(6,8) | N01632, N01633, N01634, N01639 |
| N01632 | none | positive row contradiction | C01896 |
| N01633 | none | positive row contradiction | C01897 |
| N01634 | C01898 | angle(4,-7107/131072) | N01635, N01636 |
| N01635 | C01899 | positive row contradiction | C01900 |
| N01636 | C01901 | angle(8,71/2048) | N01637, N01638 |
| N01637 | C01902 | catalogue sharp terminal(1) | C05026 |
| N01638 | C01903 | positive row contradiction | C01904 |
| N01639 | none | positive row contradiction | C01905 |
| N01640 | C01906 | angle(4,-4065/65536) | N01641, N01642 |
| N01641 | C01907 | positive row contradiction | C01908 |
| N01642 | C01909 | positive row contradiction | C01910 |
| N01643 | C01911 | angle(7,-13573/65536) | N01644, N01645 |
| N01644 | C01912 | positive row contradiction | C01913 |
| N01645 | C01914 | positive row contradiction | C01915 |
| N01646 | C01916 | positive row contradiction | C01917 |
| N01647 | C01918 | proxy(7,8) | N01648, N01649, N01654, N01655 |
| N01648 | none | positive row contradiction | C01919 |
| N01649 | C01920 | proxy(2,8) | N01650, N01651, N01652, N01653 |
| N01650 | C01921 | positive row contradiction | C01922 |
| N01651 | none | positive row contradiction | C01923 |
| N01652 | none | positive row contradiction | C01924 |
| N01653 | none | positive row contradiction | C01925 |
| N01654 | none | positive row contradiction | C01926 |
| N01655 | none | positive row contradiction | C01927 |
| N01656 | C01928 | proxy(5,8) | N01657, N01658, N01659, N01680 |
| N01657 | C01929 | positive row contradiction | C01930 |
| N01658 | C01931 | positive row contradiction | C01932 |
| N01659 | C01933 | proxy(2,7) | N01660, N01677, N01678, N01679 |
| N01660 | C01934 | proxy(4,8) | N01661, N01662, N01675, N01676 |
| N01661 | none | positive row contradiction | C01935 |
| N01662 | C01936 | angle(7,-13573/65536) | N01663, N01664 |
| N01663 | C01937 | positive row contradiction | C01938 |
| N01664 | C01939 | angle(8,13573/65536) | N01665, N01674 |
| N01665 | C01940 | sat(6,8) | N01666, N01667, N01668, N01669, N01670, N01671, N01672, N01673 |
| N01666 | C01941 | positive row contradiction | C01942 |
| N01667 | none | positive row contradiction | C01943 |
| N01668 | none | positive row contradiction | C01944 |
| N01669 | none | positive row contradiction | C01945 |
| N01670 | C01946 | positive row contradiction | C01947 |
| N01671 | none | positive row contradiction | C01948 |
| N01672 | none | positive row contradiction | C01949 |
| N01673 | none | positive row contradiction | C01950 |
| N01674 | C01951 | positive row contradiction | C01952 |
| N01675 | C01953 | positive row contradiction | C01954 |
| N01676 | none | positive row contradiction | C01955 |
| N01677 | none | positive row contradiction | C01956 |
| N01678 | none | positive row contradiction | C01957 |
| N01679 | none | positive row contradiction | C01958 |
| N01680 | C01959 | sat(6,8) | N01681, N01684, N01685, N01686, N01687, N01690, N01691, N01692 |
| N01681 | C01960 | angle(8,13573/65536) | N01682, N01683 |
| N01682 | C01961 | positive row contradiction | C01962 |
| N01683 | none | positive row contradiction | C01963 |
| N01684 | none | positive row contradiction | C01964 |
| N01685 | none | positive row contradiction | C01965 |
| N01686 | none | positive row contradiction | C01966 |
| N01687 | C01967 | angle(8,22951/131072) | N01688, N01689 |
| N01688 | C01968 | positive row contradiction | C01969 |
| N01689 | none | positive row contradiction | C01970 |
| N01690 | none | positive row contradiction | C01971 |
| N01691 | none | positive row contradiction | C01972 |
| N01692 | C01973 | angle(8,31751/131072) | N01693, N01694 |
| N01693 | C01974 | positive row contradiction | C01975 |
| N01694 | none | positive row contradiction | C01976 |
| N01695 | C01977 | angle(3,-13205/65536) | N01696, N01697 |
| N01696 | none | positive row contradiction | C01978 |
| N01697 | none | positive row contradiction | C01979 |
| N01698 | C01980 | angle(3,-13573/65536) | N01699, N01700 |
| N01699 | C01981 | positive row contradiction | C01982 |
| N01700 | C01983 | angle(7,-13573/65536) | N01701, N01794 |
| N01701 | C01984 | proxy(1,8) | N01702, N01703, N01764, N01775 |
| N01702 | none | positive row contradiction | C01985 |
| N01703 | C01986 | angle(6,-13539/65536) | N01704, N01705 |
| N01704 | none | positive row contradiction | C01987 |
| N01705 | C01988 | proxy(5,8) | N01706, N01707, N01712, N01763 |
| N01706 | none | positive row contradiction | C01989 |
| N01707 | C01990 | proxy(3,8) | N01708, N01709, N01710, N01711 |
| N01708 | none | positive row contradiction | C01991 |
| N01709 | none | positive row contradiction | C01992 |
| N01710 | C01993 | positive row contradiction | C01994 |
| N01711 | C01995 | positive row contradiction | C01996 |
| N01712 | C01997 | angle(8,13573/65536) | N01713, N01756 |
| N01713 | C01998 | proxy(2,8) | N01714, N01715, N01716, N01717 |
| N01714 | none | positive row contradiction | C01999 |
| N01715 | none | positive row contradiction | C02000 |
| N01716 | none | positive row contradiction | C02001 |
| N01717 | C02002 | sat(2,8) | N01718, N01719, N01720, N01721, N01728, N01729, N01730, N01731 |
| N01718 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N01719 | none | positive row contradiction | C02003 |
| N01720 | none | positive row contradiction | C02004 |
| N01721 | C02005 | angle(8,13573/131072) | N01722, N01727 |
| N01722 | C02006 | angle(4,-3645/65536) | N01723, N01724 |
| N01723 | C02007 | positive row contradiction | C02008 |
| N01724 | C02009 | angle(8,5199/131072) | N01725, N01726 |
| N01725 | C02010 | catalogue sharp terminal(1) | C05041 |
| N01726 | none | positive row contradiction | C02011 |
| N01727 | C02012 | positive row contradiction | C02013 |
| N01728 | none | positive row contradiction | C02014 |
| N01729 | none | positive row contradiction | C02015 |
| N01730 | none | positive row contradiction | C02016 |
| N01731 | C02017 | sat(1,4) | N01732, N01733, N01734, N01735, N01740, N01741, N01742, N01743 |
| N01732 | none | positive row contradiction | C02018 |
| N01733 | none | positive row contradiction | C02019 |
| N01734 | none | positive row contradiction | C02020 |
| N01735 | C02021 | angle(8,193/2048) | N01736, N01739 |
| N01736 | C02022 | angle(4,-1443/32768) | N01737, N01738 |
| N01737 | C02023 | positive row contradiction | C02024 |
| N01738 | C02025 | uniform sharp terminal | C05042 |
| N01739 | C02026 | positive row contradiction | C02027 |
| N01740 | none | positive row contradiction | C02028 |
| N01741 | none | positive row contradiction | C02029 |
| N01742 | none | positive row contradiction | C02030 |
| N01743 | C02031 | sat(1,7) | N01744, N01745, N01746, N01749, N01750, N01751, N01752, N01755 |
| N01744 | none | positive row contradiction | C02032 |
| N01745 | none | positive row contradiction | C02033 |
| N01746 | C02034 | angle(8,6505/131072) | N01747, N01748 |
| N01747 | C02035 | catalogue sharp terminal(2) | C05043 |
| N01748 | none | positive row contradiction | C02036 |
| N01749 | none | positive row contradiction | C02037 |
| N01750 | none | positive row contradiction | C02038 |
| N01751 | none | positive row contradiction | C02039 |
| N01752 | C02040 | angle(8,6365/131072) | N01753, N01754 |
| N01753 | C02041 | catalogue sharp terminal(2) | C05044 |
| N01754 | none | positive row contradiction | C02042 |
| N01755 | none | positive row contradiction | C02043 |
| N01756 | C02044 | proxy(6,8) | N01757, N01758, N01759, N01762 |
| N01757 | none | positive row contradiction | C02045 |
| N01758 | none | positive row contradiction | C02046 |
| N01759 | C02047 | angle(4,-7507/65536) | N01760, N01761 |
| N01760 | none | positive row contradiction | C02048 |
| N01761 | C02049 | positive row contradiction | C02050 |
| N01762 | none | positive row contradiction | C02051 |
| N01763 | C02052 | positive row contradiction | C02053 |
| N01764 | C02054 | angle(6,-13539/65536) | N01765, N01766 |
| N01765 | none | positive row contradiction | C02055 |
| N01766 | C02056 | proxy(7,8) | N01767, N01768, N01773, N01774 |
| N01767 | none | positive row contradiction | C02057 |
| N01768 | C02058 | proxy(2,8) | N01769, N01770, N01771, N01772 |
| N01769 | C02059 | positive row contradiction | C02060 |
| N01770 | none | positive row contradiction | C02061 |
| N01771 | none | positive row contradiction | C02062 |
| N01772 | none | positive row contradiction | C02063 |
| N01773 | none | positive row contradiction | C02064 |
| N01774 | none | positive row contradiction | C02065 |
| N01775 | C02066 | angle(6,-13539/65536) | N01776, N01777 |
| N01776 | none | positive row contradiction | C02067 |
| N01777 | C02068 | proxy(5,8) | N01778, N01779, N01780, N01793 |
| N01778 | C02069 | positive row contradiction | C02070 |
| N01779 | C02071 | positive row contradiction | C02072 |
| N01780 | C02073 | proxy(4,8) | N01781, N01782, N01791, N01792 |
| N01781 | none | positive row contradiction | C02074 |
| N01782 | C02075 | sat(6,8) | N01783, N01784, N01785, N01786, N01787, N01788, N01789, N01790 |
| N01783 | C02076 | positive row contradiction | C02077 |
| N01784 | none | positive row contradiction | C02078 |
| N01785 | none | positive row contradiction | C02079 |
| N01786 | none | positive row contradiction | C02080 |
| N01787 | C02081 | positive row contradiction | C02082 |
| N01788 | none | positive row contradiction | C02083 |
| N01789 | none | positive row contradiction | C02084 |
| N01790 | none | positive row contradiction | C02085 |
| N01791 | none | positive row contradiction | C02086 |
| N01792 | none | positive row contradiction | C02087 |
| N01793 | C02088 | positive row contradiction | C02089 |
| N01794 | C02090 | angle(6,-13573/65536) | N01795, N01796 |
| N01795 | C02091 | positive row contradiction | C02092 |
| N01796 | C02093 | proxy(5,8) | N01797, N01804, N01809, N01862 |
| N01797 | C02094 | proxy(4,8) | N01798, N01799, N01800, N01803 |
| N01798 | none | positive row contradiction | C02095 |
| N01799 | none | positive row contradiction | C02096 |
| N01800 | C02097 | angle(8,13573/65536) | N01801, N01802 |
| N01801 | C02098 | positive row contradiction | C02099 |
| N01802 | C02100 | positive row contradiction | C02101 |
| N01803 | none | positive row contradiction | C02102 |
| N01804 | C02103 | proxy(3,8) | N01805, N01806, N01807, N01808 |
| N01805 | none | positive row contradiction | C02104 |
| N01806 | none | positive row contradiction | C02105 |
| N01807 | C02106 | positive row contradiction | C02107 |
| N01808 | C02108 | positive row contradiction | C02109 |
| N01809 | C02110 | proxy(1,8) | N01810, N01811, N01834, N01839 |
| N01810 | none | positive row contradiction | C02111 |
| N01811 | C02112 | proxy(2,8) | N01812, N01813, N01814, N01815 |
| N01812 | none | positive row contradiction | C02113 |
| N01813 | none | positive row contradiction | C02114 |
| N01814 | none | positive row contradiction | C02115 |
| N01815 | C02116 | angle(8,13573/65536) | N01816, N01825 |
| N01816 | C02117 | proxy(6,8) | N01817, N01818, N01819, N01824 |
| N01817 | none | positive row contradiction | C02118 |
| N01818 | none | positive row contradiction | C02119 |
| N01819 | C02120 | angle(8,13573/131072) | N01820, N01823 |
| N01820 | C02121 | angle(4,-7277/131072) | N01821, N01822 |
| N01821 | C02122 | positive row contradiction | C02123 |
| N01822 | C02124 | catalogue sharp terminal(1) | C05027 |
| N01823 | C02125 | positive row contradiction | C02126 |
| N01824 | none | positive row contradiction | C02127 |
| N01825 | C02128 | sat(6,8) | N01826, N01827, N01828, N01829, N01830, N01831, N01832, N01833 |
| N01826 | none | positive row contradiction | C02129 |
| N01827 | none | positive row contradiction | C02130 |
| N01828 | none | positive row contradiction | C02131 |
| N01829 | none | positive row contradiction | C02132 |
| N01830 | none | positive row contradiction | C02133 |
| N01831 | none | positive row contradiction | C02134 |
| N01832 | none | positive row contradiction | C02135 |
| N01833 | none | positive row contradiction | C02136 |
| N01834 | C02137 | proxy(7,8) | N01835, N01836, N01837, N01838 |
| N01835 | none | positive row contradiction | C02138 |
| N01836 | C02139 | positive row contradiction | C02140 |
| N01837 | none | positive row contradiction | C02141 |
| N01838 | none | positive row contradiction | C02142 |
| N01839 | C02143 | sat(5,8) | N01840, N01841, N01842, N01843, N01844, N01845, N01846, N01861 |
| N01840 | none | positive row contradiction | C02144 |
| N01841 | C02145 | positive row contradiction | C02146 |
| N01842 | C02147 | positive row contradiction | C02148 |
| N01843 | none | positive row contradiction | C02149 |
| N01844 | C02150 | positive row contradiction | C02151 |
| N01845 | C02152 | positive row contradiction | C02153 |
| N01846 | C02154 | angle(4,-10709/65536) | N01847, N01848 |
| N01847 | none | positive row contradiction | C02155 |
| N01848 | C02156 | proxy(4,8) | N01849, N01850, N01859, N01860 |
| N01849 | none | positive row contradiction | C02157 |
| N01850 | C02158 | sat(1,8) | N01851, N01852, N01853, N01854, N01855, N01856, N01857, N01858 |
| N01851 | none | positive row contradiction | C02159 |
| N01852 | none | positive row contradiction | C02160 |
| N01853 | none | positive row contradiction | C02161 |
| N01854 | none | positive row contradiction | C02162 |
| N01855 | none | positive row contradiction | C02163 |
| N01856 | none | positive row contradiction | C02164 |
| N01857 | none | positive row contradiction | C02165 |
| N01858 | none | positive row contradiction | C02166 |
| N01859 | none | positive row contradiction | C02167 |
| N01860 | none | positive row contradiction | C02168 |
| N01861 | none | positive row contradiction | C02169 |
| N01862 | C02170 | sat(4,8) | N01863, N01864, N01865, N01866, N01867, N01868, N01869, N01870 |
| N01863 | none | positive row contradiction | C02171 |
| N01864 | C02172 | positive row contradiction | C02173 |
| N01865 | none | positive row contradiction | C02174 |
| N01866 | C02175 | positive row contradiction | C02176 |
| N01867 | none | positive row contradiction | C02177 |
| N01868 | C02178 | positive row contradiction | C02179 |
| N01869 | none | positive row contradiction | C02180 |
| N01870 | none | positive row contradiction | C02181 |
| N01871 | C02182 | angle(5,0) | N01872, N02011 |
| N01872 | C02183 | angle(3,-13573/65536) | N01873, N01874 |
| N01873 | C02184 | positive row contradiction | C02185 |
| N01874 | C02186 | proxy(1,8) | N01875, N01876, N01965, N01978 |
| N01875 | none | positive row contradiction | C02187 |
| N01876 | C02188 | angle(8,13573/65536) | N01877, N01936 |
| N01877 | C02189 | angle(6,-13539/65536) | N01878, N01879 |
| N01878 | none | positive row contradiction | C02190 |
| N01879 | C02191 | proxy(2,8) | N01880, N01881, N01882, N01883 |
| N01880 | none | positive row contradiction | C02192 |
| N01881 | none | positive row contradiction | C02193 |
| N01882 | none | positive row contradiction | C02194 |
| N01883 | C02195 | proxy(5,8) | N01884, N01885, N01886, N01935 |
| N01884 | none | positive row contradiction | C02196 |
| N01885 | C02197 | positive row contradiction | C02198 |
| N01886 | C02199 | sat(3,8) | N01887, N01896, N01897, N01898, N01899, N01932, N01933, N01934 |
| N01887 | C02200 | angle(8,13573/131072) | N01888, N01895 |
| N01888 | C02201 | proxy(6,8) | N01889, N01890, N01891, N01894 |
| N01889 | none | positive row contradiction | C02202 |
| N01890 | none | positive row contradiction | C02203 |
| N01891 | C02204 | angle(8,3349/65536) | N01892, N01893 |
| N01892 | C02205 | catalogue sharp terminal(1) | C05028 |
| N01893 | none | positive row contradiction | C02206 |
| N01894 | none | positive row contradiction | C02207 |
| N01895 | C02208 | positive row contradiction | C02209 |
| N01896 | none | positive row contradiction | C02210 |
| N01897 | none | positive row contradiction | C02211 |
| N01898 | none | positive row contradiction | C02212 |
| N01899 | C02213 | sat(1,7) | N01900, N01901, N01902, N01915, N01916, N01917, N01918, N01931 |
| N01900 | none | positive row contradiction | C02214 |
| N01901 | none | positive row contradiction | C02215 |
| N01902 | C02216 | sat(6,8) | N01903, N01904, N01905, N01908, N01909, N01910, N01911, N01914 |
| N01903 | none | positive row contradiction | C02217 |
| N01904 | none | positive row contradiction | C02218 |
| N01905 | C02219 | angle(4,2835/65536) | N01906, N01907 |
| N01906 | C02220 | uniform sharp terminal | C05029 |
| N01907 | none | positive row contradiction | C02221 |
| N01908 | none | positive row contradiction | C02222 |
| N01909 | none | positive row contradiction | C02223 |
| N01910 | none | common-axis chain [[8,0],[6,8,3]] | endpoint squared distance < 4 |
| N01911 | C02224 | angle(4,5567/131072) | N01912, N01913 |
| N01912 | C02225 | uniform sharp terminal | C05030 |
| N01913 | none | positive row contradiction | C02226 |
| N01914 | none | positive row contradiction | C02227 |
| N01915 | none | positive row contradiction | C02228 |
| N01916 | none | positive row contradiction | C02229 |
| N01917 | none | positive row contradiction | C02230 |
| N01918 | C02231 | sat(6,8) | N01919, N01920, N01921, N01924, N01925, N01926, N01927, N01930 |
| N01919 | none | positive row contradiction | C02232 |
| N01920 | none | positive row contradiction | C02233 |
| N01921 | C02234 | angle(4,2835/65536) | N01922, N01923 |
| N01922 | C02235 | uniform sharp terminal | C05031 |
| N01923 | none | positive row contradiction | C02236 |
| N01924 | none | positive row contradiction | C02237 |
| N01925 | none | positive row contradiction | C02238 |
| N01926 | none | common-axis chain [[8,0],[6,8,3]] | endpoint squared distance < 4 |
| N01927 | C02239 | angle(4,5567/131072) | N01928, N01929 |
| N01928 | C02240 | uniform sharp terminal | C05032 |
| N01929 | none | positive row contradiction | C02241 |
| N01930 | none | positive row contradiction | C02242 |
| N01931 | none | positive row contradiction | C02243 |
| N01932 | none | positive row contradiction | C02244 |
| N01933 | none | positive row contradiction | C02245 |
| N01934 | none | positive row contradiction | C02246 |
| N01935 | none | positive row contradiction | C02247 |
| N01936 | C02248 | angle(6,-13539/65536) | N01937, N01938 |
| N01937 | none | positive row contradiction | C02249 |
| N01938 | C02250 | proxy(2,8) | N01939, N01940, N01941, N01942 |
| N01939 | none | positive row contradiction | C02251 |
| N01940 | none | positive row contradiction | C02252 |
| N01941 | none | positive row contradiction | C02253 |
| N01942 | C02254 | angle(7,-13573/65536) | N01943, N01952 |
| N01943 | C02255 | sat(3,8) | N01944, N01945, N01946, N01947, N01948, N01949, N01950, N01951 |
| N01944 | C02256 | positive row contradiction | C02257 |
| N01945 | none | positive row contradiction | C02258 |
| N01946 | none | positive row contradiction | C02259 |
| N01947 | none | positive row contradiction | C02260 |
| N01948 | none | positive row contradiction | C02261 |
| N01949 | none | positive row contradiction | C02262 |
| N01950 | none | positive row contradiction | C02263 |
| N01951 | none | positive row contradiction | C02264 |
| N01952 | C02265 | proxy(5,8) | N01953, N01954, N01955, N01964 |
| N01953 | none | positive row contradiction | C02266 |
| N01954 | none | positive row contradiction | C02267 |
| N01955 | C02268 | sat(6,8) | N01956, N01957, N01958, N01959, N01960, N01961, N01962, N01963 |
| N01956 | none | positive row contradiction | C02269 |
| N01957 | none | positive row contradiction | C02270 |
| N01958 | none | positive row contradiction | C02271 |
| N01959 | none | positive row contradiction | C02272 |
| N01960 | C02273 | positive row contradiction | C02274 |
| N01961 | none | positive row contradiction | C02275 |
| N01962 | none | positive row contradiction | C02276 |
| N01963 | none | positive row contradiction | C02277 |
| N01964 | none | positive row contradiction | C02278 |
| N01965 | C02279 | angle(6,-13573/65536) | N01966, N01967 |
| N01966 | C02280 | positive row contradiction | C02281 |
| N01967 | C02282 | angle(4,13573/65536) | N01968, N01977 |
| N01968 | C02283 | proxy(7,8) | N01969, N01970, N01975, N01976 |
| N01969 | none | positive row contradiction | C02284 |
| N01970 | C02285 | proxy(2,8) | N01971, N01972, N01973, N01974 |
| N01971 | C02286 | positive row contradiction | C02287 |
| N01972 | none | positive row contradiction | C02288 |
| N01973 | none | positive row contradiction | C02289 |
| N01974 | none | positive row contradiction | C02290 |
| N01975 | none | positive row contradiction | C02291 |
| N01976 | none | positive row contradiction | C02292 |
| N01977 | C02293 | positive row contradiction | C02294 |
| N01978 | C02295 | angle(6,-13573/65536) | N01979, N01980 |
| N01979 | C02296 | positive row contradiction | C02297 |
| N01980 | C02298 | angle(4,13573/65536) | N01981, N02010 |
| N01981 | C02299 | proxy(5,8) | N01982, N01983, N01984, N02007 |
| N01982 | C02300 | positive row contradiction | C02301 |
| N01983 | C02302 | positive row contradiction | C02303 |
| N01984 | C02304 | sat(5,8) | N01985, N01986, N01987, N01988, N01989, N01990, N01991, N02006 |
| N01985 | none | positive row contradiction | C02305 |
| N01986 | C02306 | positive row contradiction | C02307 |
| N01987 | C02308 | positive row contradiction | C02309 |
| N01988 | none | positive row contradiction | C02310 |
| N01989 | C02311 | positive row contradiction | C02312 |
| N01990 | C02313 | positive row contradiction | C02314 |
| N01991 | C02315 | proxy(4,8) | N01992, N01993, N02004, N02005 |
| N01992 | none | positive row contradiction | C02316 |
| N01993 | C02317 | angle(8,13573/65536) | N01994, N02003 |
| N01994 | C02318 | sat(6,8) | N01995, N01996, N01997, N01998, N01999, N02000, N02001, N02002 |
| N01995 | C02319 | positive row contradiction | C02320 |
| N01996 | none | positive row contradiction | C02321 |
| N01997 | none | positive row contradiction | C02322 |
| N01998 | none | positive row contradiction | C02323 |
| N01999 | C02324 | positive row contradiction | C02325 |
| N02000 | none | positive row contradiction | C02326 |
| N02001 | none | positive row contradiction | C02327 |
| N02002 | none | common-axis chain [[8,1],[6,8,5]] | endpoint squared distance < 4 |
| N02003 | C02328 | positive row contradiction | C02329 |
| N02004 | none | positive row contradiction | C02330 |
| N02005 | none | positive row contradiction | C02331 |
| N02006 | none | positive row contradiction | C02332 |
| N02007 | C02333 | angle(7,-13573/65536) | N02008, N02009 |
| N02008 | none | positive row contradiction | C02334 |
| N02009 | C02335 | positive row contradiction | C02336 |
| N02010 | C02337 | positive row contradiction | C02338 |
| N02011 | C02339 | angle(2,13573/65536) | N02012, N02115 |
| N02012 | C02340 | proxy(0,8) | N02013, N02014, N02087, N02096 |
| N02013 | none | positive row contradiction | C02341 |
| N02014 | C02342 | proxy(1,8) | N02015, N02016, N02045, N02054 |
| N02015 | none | positive row contradiction | C02343 |
| N02016 | C02344 | angle(4,13573/65536) | N02017, N02044 |
| N02017 | C02345 | proxy(5,8) | N02018, N02019, N02028, N02043 |
| N02018 | none | positive row contradiction | C02346 |
| N02019 | C02347 | proxy(2,8) | N02020, N02021, N02022, N02023 |
| N02020 | none | positive row contradiction | C02348 |
| N02021 | none | positive row contradiction | C02349 |
| N02022 | none | positive row contradiction | C02350 |
| N02023 | C02351 | proxy(3,8) | N02024, N02025, N02026, N02027 |
| N02024 | none | positive row contradiction | C02352 |
| N02025 | none | positive row contradiction | C02353 |
| N02026 | none | positive row contradiction | C02354 |
| N02027 | none | positive row contradiction | C02355 |
| N02028 | C02356 | proxy(2,8) | N02029, N02030, N02031, N02032 |
| N02029 | none | positive row contradiction | C02357 |
| N02030 | none | positive row contradiction | C02358 |
| N02031 | none | positive row contradiction | C02359 |
| N02032 | C02360 | proxy(3,8) | N02033, N02040, N02041, N02042 |
| N02033 | C02361 | angle(8,13573/65536) | N02034, N02039 |
| N02034 | C02362 | angle(8,13573/131072) | N02035, N02038 |
| N02035 | C02363 | angle(8,13573/262144) | N02036, N02037 |
| N02036 | C02364 | catalogue sharp terminal(1) | C05033 |
| N02037 | C02365 | positive row contradiction | C02366 |
| N02038 | C02367 | positive row contradiction | C02368 |
| N02039 | C02369 | positive row contradiction | C02370 |
| N02040 | none | positive row contradiction | C02371 |
| N02041 | none | positive row contradiction | C02372 |
| N02042 | none | positive row contradiction | C02373 |
| N02043 | C02374 | positive row contradiction | C02375 |
| N02044 | none | positive row contradiction | C02376 |
| N02045 | C02377 | proxy(7,8) | N02046, N02047, N02052, N02053 |
| N02046 | none | positive row contradiction | C02378 |
| N02047 | C02379 | proxy(2,8) | N02048, N02049, N02050, N02051 |
| N02048 | C02380 | positive row contradiction | C02381 |
| N02049 | none | positive row contradiction | C02382 |
| N02050 | none | positive row contradiction | C02383 |
| N02051 | none | positive row contradiction | C02384 |
| N02052 | none | positive row contradiction | C02385 |
| N02053 | none | positive row contradiction | C02386 |
| N02054 | C02387 | proxy(5,8) | N02055, N02056, N02057, N02084 |
| N02055 | none | positive row contradiction | C02388 |
| N02056 | C02389 | positive row contradiction | C02390 |
| N02057 | C02391 | angle(7,-13573/65536) | N02058, N02067 |
| N02058 | C02392 | sat(5,8) | N02059, N02060, N02061, N02062, N02063, N02064, N02065, N02066 |
| N02059 | none | positive row contradiction | C02393 |
| N02060 | none | positive row contradiction | C02394 |
| N02061 | none | positive row contradiction | C02395 |
| N02062 | none | positive row contradiction | C02396 |
| N02063 | none | positive row contradiction | C02397 |
| N02064 | none | positive row contradiction | C02398 |
| N02065 | C02399 | positive row contradiction | C02400 |
| N02066 | none | positive row contradiction | C02401 |
| N02067 | C02402 | sat(4,8) | N02068, N02069, N02074, N02075, N02076, N02077, N02080, N02083 |
| N02068 | none | positive row contradiction | C02403 |
| N02069 | C02404 | proxy(6,8) | N02070, N02071, N02072, N02073 |
| N02070 | C02405 | positive row contradiction | C02406 |
| N02071 | none | positive row contradiction | C02407 |
| N02072 | none | positive row contradiction | C02408 |
| N02073 | none | positive row contradiction | C02409 |
| N02074 | C02410 | positive row contradiction | C02411 |
| N02075 | none | positive row contradiction | C02412 |
| N02076 | none | positive row contradiction | C02413 |
| N02077 | C02414 | angle(8,23605/131072) | N02078, N02079 |
| N02078 | C02415 | positive row contradiction | C02416 |
| N02079 | none | positive row contradiction | C02417 |
| N02080 | C02418 | angle(8,16751/65536) | N02081, N02082 |
| N02081 | none | positive row contradiction | C02419 |
| N02082 | C02420 | positive row contradiction | C02421 |
| N02083 | none | positive row contradiction | C02422 |
| N02084 | C02423 | angle(4,12577/65536) | N02085, N02086 |
| N02085 | C02424 | positive row contradiction | C02425 |
| N02086 | none | positive row contradiction | C02426 |
| N02087 | C02427 | proxy(2,8) | N02088, N02093, N02094, N02095 |
| N02088 | C02428 | proxy(7,8) | N02089, N02090, N02091, N02092 |
| N02089 | none | positive row contradiction | C02429 |
| N02090 | C02430 | positive row contradiction | C02431 |
| N02091 | none | positive row contradiction | C02432 |
| N02092 | none | positive row contradiction | C02433 |
| N02093 | none | positive row contradiction | C02434 |
| N02094 | none | positive row contradiction | C02435 |
| N02095 | none | positive row contradiction | C02436 |
| N02096 | C02437 | proxy(5,8) | N02097, N02098, N02099, N02100 |
| N02097 | C02438 | positive row contradiction | C02439 |
| N02098 | C02440 | positive row contradiction | C02441 |
| N02099 | none | positive row contradiction | C02442 |
| N02100 | C02443 | sat(6,8) | N02101, N02104, N02105, N02106, N02107, N02110, N02111, N02112 |
| N02101 | C02444 | angle(4,12577/65536) | N02102, N02103 |
| N02102 | C02445 | positive row contradiction | C02446 |
| N02103 | none | positive row contradiction | C02447 |
| N02104 | none | positive row contradiction | C02448 |
| N02105 | none | positive row contradiction | C02449 |
| N02106 | none | positive row contradiction | C02450 |
| N02107 | C02451 | angle(4,12577/65536) | N02108, N02109 |
| N02108 | C02452 | positive row contradiction | C02453 |
| N02109 | none | positive row contradiction | C02454 |
| N02110 | none | positive row contradiction | C02455 |
| N02111 | none | positive row contradiction | C02456 |
| N02112 | C02457 | angle(8,31751/131072) | N02113, N02114 |
| N02113 | C02458 | positive row contradiction | C02459 |
| N02114 | none | positive row contradiction | C02460 |
| N02115 | C02461 | proxy(1,8) | N02116, N02117, N02118, N02119 |
| N02116 | none | positive row contradiction | C02462 |
| N02117 | C02463 | positive row contradiction | C02464 |
| N02118 | C02465 | positive row contradiction | C02466 |
| N02119 | C02467 | positive row contradiction | C02468 |
| N02120 | C02469 | angle(3,-13573/65536) | N02121, N02122 |
| N02121 | C02470 | positive row contradiction | C02471 |
| N02122 | C02472 | angle(4,0) | N02123, N02254 |
| N02123 | C02473 | proxy(1,8) | N02124, N02125, N02204, N02221 |
| N02124 | none | positive row contradiction | C02474 |
| N02125 | C02475 | angle(6,13573/65536) | N02126, N02203 |
| N02126 | C02476 | proxy(5,8) | N02127, N02128, N02137, N02202 |
| N02127 | none | positive row contradiction | C02477 |
| N02128 | C02478 | proxy(2,8) | N02129, N02130, N02131, N02132 |
| N02129 | none | positive row contradiction | C02479 |
| N02130 | none | positive row contradiction | C02480 |
| N02131 | none | positive row contradiction | C02481 |
| N02132 | C02482 | proxy(6,8) | N02133, N02134, N02135, N02136 |
| N02133 | none | positive row contradiction | C02483 |
| N02134 | none | positive row contradiction | C02484 |
| N02135 | none | positive row contradiction | C02485 |
| N02136 | none | positive row contradiction | C02486 |
| N02137 | C02487 | sat(1,8) | N02138, N02139, N02166, N02167, N02168, N02169, N02196, N02201 |
| N02138 | none | positive row contradiction | C02488 |
| N02139 | C02489 | proxy(2,8) | N02140, N02141, N02142, N02143 |
| N02140 | none | positive row contradiction | C02490 |
| N02141 | none | positive row contradiction | C02491 |
| N02142 | none | positive row contradiction | C02492 |
| N02143 | C02493 | angle(8,13573/65536) | N02144, N02165 |
| N02144 | C02494 | sat(1,7) | N02145, N02146, N02147, N02154, N02155, N02156, N02157, N02164 |
| N02145 | none | positive row contradiction | C02495 |
| N02146 | none | positive row contradiction | C02496 |
| N02147 | C02497 | angle(4,-3921/65536) | N02148, N02149 |
| N02148 | C02498 | positive row contradiction | C02499 |
| N02149 | C02500 | angle(4,-3921/131072) | N02150, N02153 |
| N02150 | C02501 | angle(6,649/32768) | N02151, N02152 |
| N02151 | C02502 | positive row contradiction | C02503 |
| N02152 | C02504 | positive row contradiction | C02505 |
| N02153 | C02506 | uniform sharp terminal | C02507 |
| N02154 | none | positive row contradiction | C02508 |
| N02155 | none | positive row contradiction | C02509 |
| N02156 | none | positive row contradiction | C02510 |
| N02157 | C02511 | angle(4,-3921/65536) | N02158, N02159 |
| N02158 | C02512 | positive row contradiction | C02513 |
| N02159 | C02514 | angle(4,-3921/131072) | N02160, N02163 |
| N02160 | C02515 | angle(6,649/32768) | N02161, N02162 |
| N02161 | C02516 | positive row contradiction | C02517 |
| N02162 | C02518 | positive row contradiction | C02519 |
| N02163 | C02520 | uniform sharp terminal | C02521 |
| N02164 | none | positive row contradiction | C02522 |
| N02165 | none | positive row contradiction | C02523 |
| N02166 | C02524 | positive row contradiction | C02525 |
| N02167 | C02526 | positive row contradiction | C02527 |
| N02168 | none | positive row contradiction | C02528 |
| N02169 | C02529 | angle(4,-22301/131072) | N02170, N02171 |
| N02170 | none | positive row contradiction | C02530 |
| N02171 | C02531 | angle(8,13573/65536) | N02172, N02187 |
| N02172 | C02532 | proxy(2,8) | N02173, N02174, N02175, N02176 |
| N02173 | none | positive row contradiction | C02533 |
| N02174 | none | positive row contradiction | C02534 |
| N02175 | none | positive row contradiction | C02535 |
| N02176 | C02536 | angle(8,13573/131072) | N02177, N02186 |
| N02177 | C02537 | angle(8,13573/262144) | N02178, N02185 |
| N02178 | C02538 | proxy(1,4) | N02179, N02180, N02181, N02182 |
| N02179 | none | positive row contradiction | C02539 |
| N02180 | none | positive row contradiction | C02540 |
| N02181 | none | positive row contradiction | C02541 |
| N02182 | C02542 | angle(4,-2131/65536) | N02183, N02184 |
| N02183 | C02543 | positive row contradiction | C02544 |
| N02184 | C02545 | uniform sharp terminal | C02546 |
| N02185 | C02547 | positive row contradiction | C02548 |
| N02186 | C02549 | positive row contradiction | C02550 |
| N02187 | C02551 | sat(3,8) | N02188, N02189, N02190, N02191, N02192, N02193, N02194, N02195 |
| N02188 | C02552 | positive row contradiction | C02553 |
| N02189 | none | positive row contradiction | C02554 |
| N02190 | none | positive row contradiction | C02555 |
| N02191 | none | positive row contradiction | C02556 |
| N02192 | none | positive row contradiction | C02557 |
| N02193 | none | positive row contradiction | C02558 |
| N02194 | none | positive row contradiction | C02559 |
| N02195 | none | positive row contradiction | C02560 |
| N02196 | C02561 | proxy(3,8) | N02197, N02198, N02199, N02200 |
| N02197 | C02562 | positive row contradiction | C02563 |
| N02198 | none | positive row contradiction | C02564 |
| N02199 | none | positive row contradiction | C02565 |
| N02200 | none | positive row contradiction | C02566 |
| N02201 | C02567 | positive row contradiction | C02568 |
| N02202 | C02569 | positive row contradiction | C02570 |
| N02203 | C02571 | positive row contradiction | C02572 |
| N02204 | C02573 | angle(6,13573/65536) | N02205, N02220 |
| N02205 | C02574 | proxy(7,8) | N02206, N02207, N02218, N02219 |
| N02206 | none | positive row contradiction | C02575 |
| N02207 | C02576 | angle(8,13573/65536) | N02208, N02217 |
| N02208 | C02577 | sat(7,8) | N02209, N02210, N02211, N02212, N02213, N02214, N02215, N02216 |
| N02209 | none | positive row contradiction | C02578 |
| N02210 | C02579 | positive row contradiction | C02580 |
| N02211 | none | positive row contradiction | C02581 |
| N02212 | none | positive row contradiction | C02582 |
| N02213 | none | positive row contradiction | C02583 |
| N02214 | none | positive row contradiction | C02584 |
| N02215 | none | positive row contradiction | C02585 |
| N02216 | none | positive row contradiction | C02586 |
| N02217 | C02587 | positive row contradiction | C02588 |
| N02218 | none | positive row contradiction | C02589 |
| N02219 | none | positive row contradiction | C02590 |
| N02220 | C02591 | positive row contradiction | C02592 |
| N02221 | C02593 | angle(6,13573/65536) | N02222, N02253 |
| N02222 | C02594 | proxy(5,8) | N02223, N02224, N02225, N02244 |
| N02223 | C02595 | positive row contradiction | C02596 |
| N02224 | C02597 | positive row contradiction | C02598 |
| N02225 | C02599 | proxy(6,8) | N02226, N02241, N02242, N02243 |
| N02226 | C02600 | angle(7,-13573/65536) | N02227, N02230 |
| N02227 | C02601 | angle(8,29285/131072) | N02228, N02229 |
| N02228 | C02602 | positive row contradiction | C02603 |
| N02229 | none | positive row contradiction | C02604 |
| N02230 | C02605 | angle(8,13573/65536) | N02231, N02240 |
| N02231 | C02606 | sat(2,7) | N02232, N02233, N02234, N02235, N02236, N02237, N02238, N02239 |
| N02232 | C02607 | positive row contradiction | C02608 |
| N02233 | none | positive row contradiction | C02609 |
| N02234 | none | positive row contradiction | C02610 |
| N02235 | none | positive row contradiction | C02611 |
| N02236 | none | positive row contradiction | C02612 |
| N02237 | none | positive row contradiction | C02613 |
| N02238 | none | positive row contradiction | C02614 |
| N02239 | none | positive row contradiction | C02615 |
| N02240 | C02616 | positive row contradiction | C02617 |
| N02241 | none | positive row contradiction | C02618 |
| N02242 | none | positive row contradiction | C02619 |
| N02243 | none | positive row contradiction | C02620 |
| N02244 | C02621 | sat(4,8) | N02245, N02246, N02247, N02248, N02249, N02250, N02251, N02252 |
| N02245 | none | positive row contradiction | C02622 |
| N02246 | C02623 | positive row contradiction | C02624 |
| N02247 | none | positive row contradiction | C02625 |
| N02248 | C02626 | positive row contradiction | C02627 |
| N02249 | none | positive row contradiction | C02628 |
| N02250 | C02629 | positive row contradiction | C02630 |
| N02251 | none | positive row contradiction | C02631 |
| N02252 | none | positive row contradiction | C02632 |
| N02253 | C02633 | positive row contradiction | C02634 |
| N02254 | C02635 | proxy(1,8) | N02255, N02256, N02331, N02342 |
| N02255 | none | positive row contradiction | C02636 |
| N02256 | C02637 | angle(6,13573/65536) | N02257, N02330 |
| N02257 | C02638 | proxy(5,8) | N02258, N02259, N02266, N02329 |
| N02258 | none | positive row contradiction | C02639 |
| N02259 | C02640 | proxy(6,8) | N02260, N02261, N02262, N02265 |
| N02260 | none | positive row contradiction | C02641 |
| N02261 | none | positive row contradiction | C02642 |
| N02262 | C02643 | angle(8,13573/65536) | N02263, N02264 |
| N02263 | C02644 | positive row contradiction | C02645 |
| N02264 | none | positive row contradiction | C02646 |
| N02265 | none | positive row contradiction | C02647 |
| N02266 | C02648 | sat(1,8) | N02267, N02268, N02281, N02282, N02283, N02284, N02325, N02328 |
| N02267 | none | positive row contradiction | C02649 |
| N02268 | C02650 | proxy(6,8) | N02269, N02270, N02271, N02280 |
| N02269 | none | positive row contradiction | C02651 |
| N02270 | none | positive row contradiction | C02652 |
| N02271 | C02653 | proxy(2,8) | N02272, N02273, N02274, N02275 |
| N02272 | none | positive row contradiction | C02654 |
| N02273 | none | positive row contradiction | C02655 |
| N02274 | none | positive row contradiction | C02656 |
| N02275 | C02657 | angle(8,297/2048) | N02276, N02279 |
| N02276 | C02658 | angle(4,6403/131072) | N02277, N02278 |
| N02277 | C02659 | uniform sharp terminal | C02660 |
| N02278 | C02661 | positive row contradiction | C02662 |
| N02279 | none | positive row contradiction | C02663 |
| N02280 | none | positive row contradiction | C02664 |
| N02281 | C02665 | positive row contradiction | C02666 |
| N02282 | C02667 | positive row contradiction | C02668 |
| N02283 | none | positive row contradiction | C02669 |
| N02284 | C02670 | angle(8,13573/65536) | N02285, N02312 |
| N02285 | C02671 | proxy(2,8) | N02286, N02287, N02288, N02289 |
| N02286 | none | positive row contradiction | C02672 |
| N02287 | none | positive row contradiction | C02673 |
| N02288 | none | positive row contradiction | C02674 |
| N02289 | C02675 | sat(1,7) | N02290, N02291, N02292, N02299, N02300, N02301, N02302, N02311 |
| N02290 | none | positive row contradiction | C02676 |
| N02291 | none | positive row contradiction | C02677 |
| N02292 | C02678 | angle(8,13573/131072) | N02293, N02298 |
| N02293 | C02679 | angle(8,6727/131072) | N02294, N02297 |
| N02294 | C02680 | angle(4,1741/65536) | N02295, N02296 |
| N02295 | C02681 | uniform sharp terminal | C02682 |
| N02296 | C02683 | positive row contradiction | C02684 |
| N02297 | none | positive row contradiction | C02685 |
| N02298 | C02686 | positive row contradiction | C02687 |
| N02299 | none | positive row contradiction | C02688 |
| N02300 | none | positive row contradiction | C02689 |
| N02301 | none | positive row contradiction | C02690 |
| N02302 | C02691 | angle(8,13573/131072) | N02303, N02310 |
| N02303 | C02692 | proxy(1,4) | N02304, N02305, N02306, N02307 |
| N02304 | none | positive row contradiction | C02693 |
| N02305 | none | positive row contradiction | C02694 |
| N02306 | none | positive row contradiction | C02695 |
| N02307 | C02696 | angle(8,2517/65536) | N02308, N02309 |
| N02308 | C02697 | uniform sharp terminal | C02698 |
| N02309 | none | positive row contradiction | C02699 |
| N02310 | C02700 | positive row contradiction | C02701 |
| N02311 | none | positive row contradiction | C02702 |
| N02312 | C02703 | proxy(3,8) | N02313, N02322, N02323, N02324 |
| N02313 | C02704 | sat(5,8) | N02314, N02315, N02316, N02317, N02318, N02319, N02320, N02321 |
| N02314 | none | positive row contradiction | C02705 |
| N02315 | none | positive row contradiction | C02706 |
| N02316 | C02707 | positive row contradiction | C02708 |
| N02317 | none | positive row contradiction | C02709 |
| N02318 | none | positive row contradiction | C02710 |
| N02319 | none | positive row contradiction | C02711 |
| N02320 | C02712 | positive row contradiction | C02713 |
| N02321 | none | positive row contradiction | C02714 |
| N02322 | none | positive row contradiction | C02715 |
| N02323 | none | positive row contradiction | C02716 |
| N02324 | none | positive row contradiction | C02717 |
| N02325 | C02718 | angle(8,13573/65536) | N02326, N02327 |
| N02326 | C02719 | positive row contradiction | C02720 |
| N02327 | C02721 | positive row contradiction | C02722 |
| N02328 | C02723 | positive row contradiction | C02724 |
| N02329 | C02725 | positive row contradiction | C02726 |
| N02330 | C02727 | positive row contradiction | C02728 |
| N02331 | C02729 | angle(6,13573/65536) | N02332, N02341 |
| N02332 | C02730 | proxy(7,8) | N02333, N02334, N02339, N02340 |
| N02333 | none | positive row contradiction | C02731 |
| N02334 | C02732 | proxy(2,8) | N02335, N02336, N02337, N02338 |
| N02335 | C02733 | positive row contradiction | C02734 |
| N02336 | none | positive row contradiction | C02735 |
| N02337 | none | positive row contradiction | C02736 |
| N02338 | none | positive row contradiction | C02737 |
| N02339 | none | positive row contradiction | C02738 |
| N02340 | none | positive row contradiction | C02739 |
| N02341 | C02740 | positive row contradiction | C02741 |
| N02342 | C02742 | angle(6,13573/65536) | N02343, N02386 |
| N02343 | C02743 | proxy(3,8) | N02344, N02369, N02370, N02371 |
| N02344 | C02744 | proxy(5,8) | N02345, N02346, N02347, N02366 |
| N02345 | C02745 | positive row contradiction | C02746 |
| N02346 | none | positive row contradiction | C02747 |
| N02347 | C02748 | sat(5,8) | N02348, N02349, N02350, N02351, N02352, N02353, N02354, N02365 |
| N02348 | none | positive row contradiction | C02749 |
| N02349 | none | positive row contradiction | C02750 |
| N02350 | C02751 | positive row contradiction | C02752 |
| N02351 | none | positive row contradiction | C02753 |
| N02352 | C02754 | positive row contradiction | C02755 |
| N02353 | none | positive row contradiction | C02756 |
| N02354 | C02757 | angle(8,13257/65536) | N02355, N02364 |
| N02355 | C02758 | sat(1,8) | N02356, N02357, N02358, N02359, N02360, N02361, N02362, N02363 |
| N02356 | none | positive row contradiction | C02759 |
| N02357 | none | positive row contradiction | C02760 |
| N02358 | none | positive row contradiction | C02761 |
| N02359 | none | positive row contradiction | C02762 |
| N02360 | none | positive row contradiction | C02763 |
| N02361 | none | positive row contradiction | C02764 |
| N02362 | none | positive row contradiction | C02765 |
| N02363 | none | positive row contradiction | C02766 |
| N02364 | C02767 | positive row contradiction | C02768 |
| N02365 | none | positive row contradiction | C02769 |
| N02366 | C02770 | angle(7,-13573/65536) | N02367, N02368 |
| N02367 | none | positive row contradiction | C02771 |
| N02368 | C02772 | positive row contradiction | C02773 |
| N02369 | none | positive row contradiction | C02774 |
| N02370 | none | positive row contradiction | C02775 |
| N02371 | C02776 | angle(7,-13573/65536) | N02372, N02381 |
| N02372 | C02777 | proxy(4,8) | N02373, N02374, N02379, N02380 |
| N02373 | none | positive row contradiction | C02778 |
| N02374 | C02779 | proxy(5,8) | N02375, N02376, N02377, N02378 |
| N02375 | none | positive row contradiction | C02780 |
| N02376 | none | positive row contradiction | C02781 |
| N02377 | none | positive row contradiction | C02782 |
| N02378 | C02783 | positive row contradiction | C02784 |
| N02379 | none | positive row contradiction | C02785 |
| N02380 | none | positive row contradiction | C02786 |
| N02381 | C02787 | proxy(5,8) | N02382, N02383, N02384, N02385 |
| N02382 | C02788 | positive row contradiction | C02789 |
| N02383 | none | positive row contradiction | C02790 |
| N02384 | none | positive row contradiction | C02791 |
| N02385 | C02792 | positive row contradiction | C02793 |
| N02386 | C02794 | positive row contradiction | C02795 |
| N02387 | C02796 | angle(6,0) | N02388, N02731 |
| N02388 | C02797 | angle(3,-13573/65536) | N02389, N02390 |
| N02389 | C02798 | positive row contradiction | C02799 |
| N02390 | C02800 | angle(4,0) | N02391, N02590 |
| N02391 | C02801 | angle(6,-13573/65536) | N02392, N02393 |
| N02392 | none | positive row contradiction | C02802 |
| N02393 | C02803 | angle(8,0) | N02394, N02451 |
| N02394 | C02804 | proxy(1,8) | N02395, N02396, N02417, N02432 |
| N02395 | none | positive row contradiction | C02805 |
| N02396 | C02806 | proxy(6,8) | N02397, N02398, N02399, N02416 |
| N02397 | none | positive row contradiction | C02807 |
| N02398 | none | positive row contradiction | C02808 |
| N02399 | C02809 | angle(4,-9965/65536) | N02400, N02401 |
| N02400 | none | positive row contradiction | C02810 |
| N02401 | C02811 | proxy(3,8) | N02402, N02413, N02414, N02415 |
| N02402 | C02812 | proxy(5,8) | N02403, N02404, N02405, N02412 |
| N02403 | none | positive row contradiction | C02813 |
| N02404 | none | positive row contradiction | C02814 |
| N02405 | C02815 | angle(8,-10345/65536) | N02406, N02407 |
| N02406 | none | positive row contradiction | C02816 |
| N02407 | C02817 | angle(8,-4287/65536) | N02408, N02409 |
| N02408 | C02818 | positive row contradiction | C02819 |
| N02409 | C02820 | angle(8,-4287/131072) | N02410, N02411 |
| N02410 | C02821 | positive row contradiction | C02822 |
| N02411 | C02823 | uniform sharp terminal | C02824 |
| N02412 | none | positive row contradiction | C02825 |
| N02413 | none | positive row contradiction | C02826 |
| N02414 | none | positive row contradiction | C02827 |
| N02415 | none | positive row contradiction | C02828 |
| N02416 | none | positive row contradiction | C02829 |
| N02417 | C02830 | angle(8,-13573/65536) | N02418, N02423 |
| N02418 | C02831 | proxy(7,8) | N02419, N02420, N02421, N02422 |
| N02419 | none | positive row contradiction | C02832 |
| N02420 | C02833 | positive row contradiction | C02834 |
| N02421 | none | positive row contradiction | C02835 |
| N02422 | none | positive row contradiction | C02836 |
| N02423 | C02837 | proxy(2,8) | N02424, N02429, N02430, N02431 |
| N02424 | C02838 | proxy(7,8) | N02425, N02426, N02427, N02428 |
| N02425 | none | positive row contradiction | C02839 |
| N02426 | none | positive row contradiction | C02840 |
| N02427 | none | positive row contradiction | C02841 |
| N02428 | none | positive row contradiction | C02842 |
| N02429 | none | positive row contradiction | C02843 |
| N02430 | none | positive row contradiction | C02844 |
| N02431 | none | positive row contradiction | C02845 |
| N02432 | C02846 | proxy(6,8) | N02433, N02448, N02449, N02450 |
| N02433 | C02847 | proxy(5,8) | N02434, N02435, N02436, N02447 |
| N02434 | C02848 | positive row contradiction | C02849 |
| N02435 | none | positive row contradiction | C02850 |
| N02436 | C02851 | angle(7,13573/65536) | N02437, N02446 |
| N02437 | C02852 | sat(5,8) | N02438, N02439, N02440, N02441, N02442, N02443, N02444, N02445 |
| N02438 | none | positive row contradiction | C02853 |
| N02439 | none | positive row contradiction | C02854 |
| N02440 | none | positive row contradiction | C02855 |
| N02441 | none | positive row contradiction | C02856 |
| N02442 | none | positive row contradiction | C02857 |
| N02443 | none | positive row contradiction | C02858 |
| N02444 | C02859 | positive row contradiction | C02860 |
| N02445 | none | positive row contradiction | C02861 |
| N02446 | C02862 | positive row contradiction | C02863 |
| N02447 | C02864 | positive row contradiction | C02865 |
| N02448 | none | positive row contradiction | C02866 |
| N02449 | none | positive row contradiction | C02867 |
| N02450 | none | positive row contradiction | C02868 |
| N02451 | C02869 | proxy(1,8) | N02452, N02453, N02562, N02571 |
| N02452 | none | positive row contradiction | C02870 |
| N02453 | C02871 | angle(7,13573/65536) | N02454, N02535 |
| N02454 | C02872 | proxy(2,8) | N02455, N02456, N02457, N02458 |
| N02455 | none | positive row contradiction | C02873 |
| N02456 | none | positive row contradiction | C02874 |
| N02457 | none | positive row contradiction | C02875 |
| N02458 | C02876 | angle(8,13573/65536) | N02459, N02530 |
| N02459 | C02877 | proxy(5,8) | N02460, N02461, N02462, N02529 |
| N02460 | none | positive row contradiction | C02878 |
| N02461 | C02879 | positive row contradiction | C02880 |
| N02462 | C02881 | angle(8,13573/131072) | N02463, N02520 |
| N02463 | C02882 | sat(2,7) | N02464, N02489, N02490, N02491, N02492, N02517, N02518, N02519 |
| N02464 | C02883 | sat(1,7) | N02465, N02466, N02467, N02472, N02473, N02474, N02475, N02488 |
| N02465 | none | positive row contradiction | C02884 |
| N02466 | none | positive row contradiction | C02885 |
| N02467 | C02886 | angle(8,2121/65536) | N02468, N02471 |
| N02468 | C02887 | angle(4,-3421/131072) | N02469, N02470 |
| N02469 | C02888 | uniform sharp terminal | C02889 |
| N02470 | C02890 | uniform sharp terminal | C02891 |
| N02471 | none | positive row contradiction | C02892 |
| N02472 | none | positive row contradiction | C02893 |
| N02473 | none | positive row contradiction | C02894 |
| N02474 | none | positive row contradiction | C02895 |
| N02475 | C02896 | sat(1,4) | N02476, N02477, N02478, N02479, N02482, N02483, N02484, N02485 |
| N02476 | none | positive row contradiction | C02897 |
| N02477 | none | positive row contradiction | C02898 |
| N02478 | none | positive row contradiction | C02899 |
| N02479 | C02900 | angle(4,-3421/131072) | N02480, N02481 |
| N02480 | C02901 | uniform sharp terminal | C02902 |
| N02481 | C02903 | uniform sharp terminal | C02904 |
| N02482 | none | positive row contradiction | C02905 |
| N02483 | none | positive row contradiction | C02906 |
| N02484 | none | positive row contradiction | C02907 |
| N02485 | C02908 | angle(4,-3421/131072) | N02486, N02487 |
| N02486 | C02909 | uniform sharp terminal | C02910 |
| N02487 | C02911 | uniform sharp terminal | C02912 |
| N02488 | none | positive row contradiction | C02913 |
| N02489 | none | positive row contradiction | C02914 |
| N02490 | none | positive row contradiction | C02915 |
| N02491 | none | positive row contradiction | C02916 |
| N02492 | C02917 | sat(1,7) | N02493, N02494, N02495, N02500, N02501, N02502, N02503, N02516 |
| N02493 | none | positive row contradiction | C02918 |
| N02494 | none | positive row contradiction | C02919 |
| N02495 | C02920 | angle(8,4267/131072) | N02496, N02499 |
| N02496 | C02921 | angle(4,-3421/131072) | N02497, N02498 |
| N02497 | C02922 | uniform sharp terminal | C02923 |
| N02498 | C02924 | uniform sharp terminal | C02925 |
| N02499 | none | positive row contradiction | C02926 |
| N02500 | none | positive row contradiction | C02927 |
| N02501 | none | positive row contradiction | C02928 |
| N02502 | none | common-axis chain [[7,0],[1,7,2]] | endpoint squared distance < 4 |
| N02503 | C02929 | sat(1,4) | N02504, N02505, N02506, N02507, N02510, N02511, N02512, N02513 |
| N02504 | none | positive row contradiction | C02930 |
| N02505 | none | positive row contradiction | C02931 |
| N02506 | none | positive row contradiction | C02932 |
| N02507 | C02933 | angle(4,-3421/131072) | N02508, N02509 |
| N02508 | C02934 | uniform sharp terminal | C02935 |
| N02509 | C02936 | uniform sharp terminal | C02937 |
| N02510 | none | positive row contradiction | C02938 |
| N02511 | none | positive row contradiction | C02939 |
| N02512 | none | positive row contradiction | C02940 |
| N02513 | C02941 | angle(4,-3421/131072) | N02514, N02515 |
| N02514 | C02942 | uniform sharp terminal | C02943 |
| N02515 | C02944 | uniform sharp terminal | C02945 |
| N02516 | none | positive row contradiction | C02946 |
| N02517 | none | positive row contradiction | C02947 |
| N02518 | none | positive row contradiction | C02948 |
| N02519 | none | positive row contradiction | C02949 |
| N02520 | C02950 | sat(6,8) | N02521, N02522, N02523, N02524, N02525, N02526, N02527, N02528 |
| N02521 | none | positive row contradiction | C02951 |
| N02522 | none | positive row contradiction | C02952 |
| N02523 | none | positive row contradiction | C02953 |
| N02524 | none | positive row contradiction | C02954 |
| N02525 | none | positive row contradiction | C02955 |
| N02526 | none | positive row contradiction | C02956 |
| N02527 | none | positive row contradiction | C02957 |
| N02528 | none | positive row contradiction | C02958 |
| N02529 | none | positive row contradiction | C02959 |
| N02530 | C02960 | proxy(5,8) | N02531, N02532, N02533, N02534 |
| N02531 | none | positive row contradiction | C02961 |
| N02532 | none | positive row contradiction | C02962 |
| N02533 | C02963 | positive row contradiction | C02964 |
| N02534 | none | positive row contradiction | C02965 |
| N02535 | C02966 | proxy(2,8) | N02536, N02537, N02538, N02539 |
| N02536 | none | positive row contradiction | C02967 |
| N02537 | none | positive row contradiction | C02968 |
| N02538 | none | positive row contradiction | C02969 |
| N02539 | C02970 | angle(8,13573/65536) | N02540, N02557 |
| N02540 | C02971 | angle(8,13573/131072) | N02541, N02552 |
| N02541 | C02972 | angle(4,-3409/65536) | N02542, N02543 |
| N02542 | C02973 | positive row contradiction | C02974 |
| N02543 | C02975 | proxy(6,8) | N02544, N02545, N02546, N02551 |
| N02544 | none | positive row contradiction | C02976 |
| N02545 | none | positive row contradiction | C02977 |
| N02546 | C02978 | angle(8,3385/65536) | N02547, N02550 |
| N02547 | C02979 | angle(4,-3409/131072) | N02548, N02549 |
| N02548 | C02980 | positive row contradiction | C02981 |
| N02549 | C02982 | uniform sharp terminal | C02983 |
| N02550 | none | positive row contradiction | C02984 |
| N02551 | none | positive row contradiction | C02985 |
| N02552 | C02986 | proxy(5,8) | N02553, N02554, N02555, N02556 |
| N02553 | none | positive row contradiction | C02987 |
| N02554 | none | positive row contradiction | C02988 |
| N02555 | C02989 | positive row contradiction | C02990 |
| N02556 | none | positive row contradiction | C02991 |
| N02557 | C02992 | proxy(6,8) | N02558, N02559, N02560, N02561 |
| N02558 | none | positive row contradiction | C02993 |
| N02559 | none | positive row contradiction | C02994 |
| N02560 | C02995 | positive row contradiction | C02996 |
| N02561 | none | positive row contradiction | C02997 |
| N02562 | C02998 | proxy(2,8) | N02563, N02568, N02569, N02570 |
| N02563 | C02999 | proxy(7,8) | N02564, N02565, N02566, N02567 |
| N02564 | none | positive row contradiction | C03000 |
| N02565 | C03001 | positive row contradiction | C03002 |
| N02566 | none | positive row contradiction | C03003 |
| N02567 | none | positive row contradiction | C03004 |
| N02568 | none | positive row contradiction | C03005 |
| N02569 | none | positive row contradiction | C03006 |
| N02570 | none | positive row contradiction | C03007 |
| N02571 | C03008 | proxy(5,8) | N02572, N02573, N02574, N02589 |
| N02572 | C03009 | positive row contradiction | C03010 |
| N02573 | C03011 | positive row contradiction | C03012 |
| N02574 | C03013 | sat(5,8) | N02575, N02576, N02577, N02578, N02579, N02580, N02581, N02588 |
| N02575 | none | positive row contradiction | C03014 |
| N02576 | none | positive row contradiction | C03015 |
| N02577 | C03016 | positive row contradiction | C03017 |
| N02578 | none | positive row contradiction | C03018 |
| N02579 | C03019 | positive row contradiction | C03020 |
| N02580 | none | positive row contradiction | C03021 |
| N02581 | C03022 | angle(7,13573/65536) | N02582, N02587 |
| N02582 | C03023 | proxy(6,8) | N02583, N02584, N02585, N02586 |
| N02583 | C03024 | positive row contradiction | C03025 |
| N02584 | none | positive row contradiction | C03026 |
| N02585 | none | positive row contradiction | C03027 |
| N02586 | none | positive row contradiction | C03028 |
| N02587 | C03029 | positive row contradiction | C03030 |
| N02588 | none | positive row contradiction | C03031 |
| N02589 | C03032 | positive row contradiction | C03033 |
| N02590 | C03034 | angle(6,-13573/65536) | N02591, N02592 |
| N02591 | none | positive row contradiction | C03035 |
| N02592 | C03036 | angle(8,0) | N02593, N02660 |
| N02593 | C03037 | proxy(1,8) | N02594, N02595, N02630, N02645 |
| N02594 | none | positive row contradiction | C03038 |
| N02595 | C03039 | angle(8,-13573/65536) | N02596, N02603 |
| N02596 | C03040 | proxy(6,8) | N02597, N02598, N02599, N02602 |
| N02597 | none | positive row contradiction | C03041 |
| N02598 | none | positive row contradiction | C03042 |
| N02599 | C03043 | angle(8,-40719/131072) | N02600, N02601 |
| N02600 | C03044 | positive row contradiction | C03045 |
| N02601 | C03046 | positive row contradiction | C03047 |
| N02602 | none | positive row contradiction | C03048 |
| N02603 | C03049 | proxy(5,8) | N02604, N02605, N02610, N02629 |
| N02604 | none | positive row contradiction | C03050 |
| N02605 | C03051 | proxy(6,8) | N02606, N02607, N02608, N02609 |
| N02606 | none | positive row contradiction | C03052 |
| N02607 | none | positive row contradiction | C03053 |
| N02608 | C03054 | positive row contradiction | C03055 |
| N02609 | none | positive row contradiction | C03056 |
| N02610 | C03057 | proxy(2,8) | N02611, N02612, N02613, N02614 |
| N02611 | none | positive row contradiction | C03058 |
| N02612 | none | positive row contradiction | C03059 |
| N02613 | none | positive row contradiction | C03060 |
| N02614 | C03061 | proxy(6,8) | N02615, N02616, N02617, N02628 |
| N02615 | none | positive row contradiction | C03062 |
| N02616 | none | positive row contradiction | C03063 |
| N02617 | C03064 | angle(8,-13573/131072) | N02618, N02619 |
| N02618 | C03065 | positive row contradiction | C03066 |
| N02619 | C03067 | angle(8,-13573/262144) | N02620, N02621 |
| N02620 | C03068 | positive row contradiction | C03069 |
| N02621 | C03070 | angle(7,13573/65536) | N02622, N02625 |
| N02622 | C03071 | angle(8,-3383/131072) | N02623, N02624 |
| N02623 | C03072 | positive row contradiction | C03073 |
| N02624 | C03074 | uniform sharp terminal | C03075 |
| N02625 | C03076 | angle(8,-3383/131072) | N02626, N02627 |
| N02626 | C03077 | positive row contradiction | C03078 |
| N02627 | C03079 | uniform sharp terminal | C03080 |
| N02628 | none | positive row contradiction | C03081 |
| N02629 | C03082 | positive row contradiction | C03083 |
| N02630 | C03084 | angle(8,-13573/65536) | N02631, N02636 |
| N02631 | C03085 | proxy(7,8) | N02632, N02633, N02634, N02635 |
| N02632 | none | positive row contradiction | C03086 |
| N02633 | C03087 | positive row contradiction | C03088 |
| N02634 | none | positive row contradiction | C03089 |
| N02635 | none | positive row contradiction | C03090 |
| N02636 | C03091 | proxy(2,8) | N02637, N02642, N02643, N02644 |
| N02637 | C03092 | proxy(7,8) | N02638, N02639, N02640, N02641 |
| N02638 | none | positive row contradiction | C03093 |
| N02639 | none | positive row contradiction | C03094 |
| N02640 | none | positive row contradiction | C03095 |
| N02641 | none | positive row contradiction | C03096 |
| N02642 | none | positive row contradiction | C03097 |
| N02643 | none | positive row contradiction | C03098 |
| N02644 | none | positive row contradiction | C03099 |
| N02645 | C03100 | angle(4,24297/131072) | N02646, N02659 |
| N02646 | C03101 | proxy(6,8) | N02647, N02656, N02657, N02658 |
| N02647 | C03102 | proxy(5,8) | N02648, N02649, N02650, N02655 |
| N02648 | none | positive row contradiction | C03103 |
| N02649 | none | positive row contradiction | C03104 |
| N02650 | C03105 | proxy(4,8) | N02651, N02652, N02653, N02654 |
| N02651 | none | positive row contradiction | C03106 |
| N02652 | C03107 | positive row contradiction | C03108 |
| N02653 | none | positive row contradiction | C03109 |
| N02654 | none | positive row contradiction | C03110 |
| N02655 | C03111 | positive row contradiction | C03112 |
| N02656 | none | positive row contradiction | C03113 |
| N02657 | none | positive row contradiction | C03114 |
| N02658 | none | positive row contradiction | C03115 |
| N02659 | none | positive row contradiction | C03116 |
| N02660 | C03117 | proxy(1,8) | N02661, N02662, N02701, N02718 |
| N02661 | none | positive row contradiction | C03118 |
| N02662 | C03119 | proxy(5,8) | N02663, N02664, N02675, N02700 |
| N02663 | none | positive row contradiction | C03120 |
| N02664 | C03121 | angle(8,13573/65536) | N02665, N02670 |
| N02665 | C03122 | proxy(6,8) | N02666, N02667, N02668, N02669 |
| N02666 | none | positive row contradiction | C03123 |
| N02667 | none | positive row contradiction | C03124 |
| N02668 | C03125 | positive row contradiction | C03126 |
| N02669 | none | positive row contradiction | C03127 |
| N02670 | C03128 | proxy(6,8) | N02671, N02672, N02673, N02674 |
| N02671 | none | positive row contradiction | C03129 |
| N02672 | none | positive row contradiction | C03130 |
| N02673 | C03131 | positive row contradiction | C03132 |
| N02674 | none | positive row contradiction | C03133 |
| N02675 | C03134 | proxy(6,8) | N02676, N02677, N02678, N02699 |
| N02676 | none | positive row contradiction | C03135 |
| N02677 | none | positive row contradiction | C03136 |
| N02678 | C03137 | proxy(3,8) | N02679, N02696, N02697, N02698 |
| N02679 | C03138 | sat(2,8) | N02680, N02681, N02682, N02683, N02688, N02689, N02690, N02691 |
| N02680 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N02681 | none | positive row contradiction | C03139 |
| N02682 | none | positive row contradiction | C03140 |
| N02683 | C03141 | angle(8,19469/131072) | N02684, N02687 |
| N02684 | C03142 | angle(8,909/32768) | N02685, N02686 |
| N02685 | C03143 | uniform sharp terminal | C03144 |
| N02686 | none | positive row contradiction | C03145 |
| N02687 | none | positive row contradiction | C03146 |
| N02688 | none | positive row contradiction | C03147 |
| N02689 | none | positive row contradiction | C03148 |
| N02690 | none | positive row contradiction | C03149 |
| N02691 | C03150 | angle(8,4095/32768) | N02692, N02695 |
| N02692 | C03151 | angle(4,3633/131072) | N02693, N02694 |
| N02693 | C03152 | uniform sharp terminal | C03153 |
| N02694 | C03154 | positive row contradiction | C03155 |
| N02695 | none | positive row contradiction | C03156 |
| N02696 | none | positive row contradiction | C03157 |
| N02697 | none | positive row contradiction | C03158 |
| N02698 | none | positive row contradiction | C03159 |
| N02699 | none | positive row contradiction | C03160 |
| N02700 | none | positive row contradiction | C03161 |
| N02701 | C03162 | angle(8,13573/65536) | N02702, N02711 |
| N02702 | C03163 | proxy(2,8) | N02703, N02708, N02709, N02710 |
| N02703 | C03164 | proxy(7,8) | N02704, N02705, N02706, N02707 |
| N02704 | none | positive row contradiction | C03165 |
| N02705 | none | positive row contradiction | C03166 |
| N02706 | none | positive row contradiction | C03167 |
| N02707 | none | positive row contradiction | C03168 |
| N02708 | none | positive row contradiction | C03169 |
| N02709 | none | positive row contradiction | C03170 |
| N02710 | none | positive row contradiction | C03171 |
| N02711 | C03172 | proxy(2,8) | N02712, N02715, N02716, N02717 |
| N02712 | C03173 | angle(7,13573/65536) | N02713, N02714 |
| N02713 | C03174 | positive row contradiction | C03175 |
| N02714 | C03176 | positive row contradiction | C03177 |
| N02715 | none | positive row contradiction | C03178 |
| N02716 | none | positive row contradiction | C03179 |
| N02717 | none | positive row contradiction | C03180 |
| N02718 | C03181 | angle(4,24297/131072) | N02719, N02730 |
| N02719 | C03182 | proxy(5,8) | N02720, N02721, N02722, N02729 |
| N02720 | C03183 | positive row contradiction | C03184 |
| N02721 | C03185 | positive row contradiction | C03186 |
| N02722 | C03187 | proxy(4,8) | N02723, N02724, N02727, N02728 |
| N02723 | none | positive row contradiction | C03188 |
| N02724 | C03189 | angle(8,14133/65536) | N02725, N02726 |
| N02725 | C03190 | positive row contradiction | C03191 |
| N02726 | C03192 | positive row contradiction | C03193 |
| N02727 | none | positive row contradiction | C03194 |
| N02728 | none | positive row contradiction | C03195 |
| N02729 | C03196 | positive row contradiction | C03197 |
| N02730 | none | positive row contradiction | C03198 |
| N02731 | C03199 | angle(5,0) | N02732, N03279 |
| N02732 | none | angle(8,0) | N02733, N03072 |
| N02733 | C03200 | angle(4,0) | N02734, N02905 |
| N02734 | C03201 | angle(3,-13573/65536) | N02735, N02736 |
| N02735 | C03202 | positive row contradiction | C03203 |
| N02736 | C03204 | proxy(1,8) | N02737, N02738, N02853, N02866 |
| N02737 | none | positive row contradiction | C03205 |
| N02738 | C03206 | angle(4,-13573/65536) | N02739, N02744 |
| N02739 | C03207 | proxy(5,8) | N02740, N02741, N02742, N02743 |
| N02740 | none | positive row contradiction | C03208 |
| N02741 | C03209 | positive row contradiction | C03210 |
| N02742 | C03211 | positive row contradiction | C03212 |
| N02743 | C03213 | positive row contradiction | C03214 |
| N02744 | C03215 | proxy(2,8) | N02745, N02746, N02747, N02748 |
| N02745 | none | positive row contradiction | C03216 |
| N02746 | C03217 | positive row contradiction | C03218 |
| N02747 | none | positive row contradiction | C03219 |
| N02748 | C03220 | proxy(5,8) | N02749, N02750, N02755, N02852 |
| N02749 | none | positive row contradiction | C03221 |
| N02750 | C03222 | proxy(6,8) | N02751, N02752, N02753, N02754 |
| N02751 | none | positive row contradiction | C03223 |
| N02752 | none | positive row contradiction | C03224 |
| N02753 | C03225 | positive row contradiction | C03226 |
| N02754 | none | positive row contradiction | C03227 |
| N02755 | C03228 | angle(8,-13573/65536) | N02756, N02765 |
| N02756 | C03229 | sat(5,8) | N02757, N02758, N02759, N02760, N02761, N02762, N02763, N02764 |
| N02757 | none | positive row contradiction | C03230 |
| N02758 | none | positive row contradiction | C03231 |
| N02759 | C03232 | positive row contradiction | C03233 |
| N02760 | none | positive row contradiction | C03234 |
| N02761 | none | positive row contradiction | C03235 |
| N02762 | C03236 | positive row contradiction | C03237 |
| N02763 | C03238 | positive row contradiction | C03239 |
| N02764 | none | positive row contradiction | C03240 |
| N02765 | C03241 | sat(3,8) | N02766, N02819, N02820, N02821, N02822, N02849, N02850, N02851 |
| N02766 | C03242 | angle(8,-13573/131072) | N02767, N02770 |
| N02767 | C03243 | angle(7,13573/65536) | N02768, N02769 |
| N02768 | C03244 | positive row contradiction | C03245 |
| N02769 | none | positive row contradiction | C03246 |
| N02770 | C03247 | sat(2,7) | N02771, N02788, N02789, N02790, N02791, N02816, N02817, N02818 |
| N02771 | C03248 | angle(4,-7393/131072) | N02772, N02773 |
| N02772 | C03249 | positive row contradiction | C03250 |
| N02773 | C03251 | angle(7,13573/65536) | N02774, N02781 |
| N02774 | C03252 | angle(8,-6071/131072) | N02775, N02776 |
| N02775 | C03253 | positive row contradiction | C03254 |
| N02776 | C03255 | angle(4,-7393/262144) | N02777, N02780 |
| N02777 | C03256 | angle(8,-6071/262144) | N02778, N02779 |
| N02778 | C03257 | uniform sharp terminal from box | C03257 |
| N02779 | C03258 | positive row contradiction | C03259 |
| N02780 | C03260 | uniform sharp terminal | C03261 |
| N02781 | C03262 | angle(8,-5799/131072) | N02782, N02783 |
| N02782 | C03263 | positive row contradiction | C03264 |
| N02783 | C03265 | angle(4,-7393/262144) | N02784, N02787 |
| N02784 | C03266 | angle(8,-325/16384) | N02785, N02786 |
| N02785 | C03267 | positive row contradiction | C03268 |
| N02786 | C03269 | positive row contradiction | C03270 |
| N02787 | C03271 | uniform sharp terminal | C03272 |
| N02788 | none | positive row contradiction | C03273 |
| N02789 | none | positive row contradiction | C03274 |
| N02790 | none | positive row contradiction | C03275 |
| N02791 | C03276 | sat(1,7) | N02792, N02793, N02794, N02803, N02804, N02805, N02806, N02815 |
| N02792 | none | positive row contradiction | C03277 |
| N02793 | none | positive row contradiction | C03278 |
| N02794 | C03279 | angle(8,-13573/262144) | N02795, N02796 |
| N02795 | C03280 | positive row contradiction | C03281 |
| N02796 | C03282 | angle(4,-713/16384) | N02797, N02798 |
| N02797 | C03283 | positive row contradiction | C03284 |
| N02798 | C03285 | angle(8,-13573/524288) | N02799, N02802 |
| N02799 | C03286 | angle(4,-713/32768) | N02800, N02801 |
| N02800 | C03287 | uniform sharp terminal from box | C03287 |
| N02801 | C03288 | uniform sharp terminal from box | C03288 |
| N02802 | C03289 | uniform sharp terminal | C03290 |
| N02803 | none | positive row contradiction | C03291 |
| N02804 | none | positive row contradiction | C03292 |
| N02805 | none | common-axis chain [[7,0],[1,7,2]] | endpoint squared distance < 4 |
| N02806 | C03293 | angle(8,-13573/262144) | N02807, N02808 |
| N02807 | C03294 | positive row contradiction | C03295 |
| N02808 | C03296 | angle(4,-713/16384) | N02809, N02810 |
| N02809 | C03297 | positive row contradiction | C03298 |
| N02810 | C03299 | angle(8,-13573/524288) | N02811, N02814 |
| N02811 | C03300 | angle(4,-713/32768) | N02812, N02813 |
| N02812 | C03301 | uniform sharp terminal from box | C03301 |
| N02813 | C03302 | uniform sharp terminal from box | C03302 |
| N02814 | C03303 | uniform sharp terminal | C03304 |
| N02815 | none | positive row contradiction | C03305 |
| N02816 | none | positive row contradiction | C03306 |
| N02817 | none | positive row contradiction | C03307 |
| N02818 | C03308 | positive row contradiction | C03309 |
| N02819 | none | positive row contradiction | C03310 |
| N02820 | none | positive row contradiction | C03311 |
| N02821 | none | positive row contradiction | C03312 |
| N02822 | C03313 | angle(8,-13573/131072) | N02823, N02824 |
| N02823 | C03314 | positive row contradiction | C03315 |
| N02824 | C03316 | sat(1,7) | N02825, N02826, N02827, N02836, N02837, N02838, N02839, N02848 |
| N02825 | none | positive row contradiction | C03317 |
| N02826 | none | positive row contradiction | C03318 |
| N02827 | C03319 | angle(4,-7393/131072) | N02828, N02829 |
| N02828 | C03320 | positive row contradiction | C03321 |
| N02829 | C03322 | angle(8,-6415/131072) | N02830, N02831 |
| N02830 | C03323 | positive row contradiction | C03324 |
| N02831 | C03325 | angle(4,-7393/262144) | N02832, N02835 |
| N02832 | C03326 | angle(8,-6415/262144) | N02833, N02834 |
| N02833 | C03327 | positive row contradiction | C03328 |
| N02834 | C03329 | positive row contradiction | C03330 |
| N02835 | C03331 | uniform sharp terminal | C03332 |
| N02836 | none | positive row contradiction | C03333 |
| N02837 | C03334 | positive row contradiction | C03335 |
| N02838 | none | positive row contradiction | C03336 |
| N02839 | C03337 | angle(4,-7393/131072) | N02840, N02841 |
| N02840 | C03338 | positive row contradiction | C03339 |
| N02841 | C03340 | angle(8,-1603/32768) | N02842, N02843 |
| N02842 | C03341 | positive row contradiction | C03342 |
| N02843 | C03343 | angle(4,-7393/262144) | N02844, N02847 |
| N02844 | C03344 | angle(8,-1603/65536) | N02845, N02846 |
| N02845 | C03345 | positive row contradiction | C03346 |
| N02846 | C03347 | positive row contradiction | C03348 |
| N02847 | C03349 | uniform sharp terminal | C03350 |
| N02848 | none | positive row contradiction | C03351 |
| N02849 | none | positive row contradiction | C03352 |
| N02850 | none | positive row contradiction | C03353 |
| N02851 | none | positive row contradiction | C03354 |
| N02852 | C03355 | positive row contradiction | C03356 |
| N02853 | C03357 | proxy(7,8) | N02854, N02855, N02864, N02865 |
| N02854 | none | positive row contradiction | C03358 |
| N02855 | C03359 | angle(4,-13573/65536) | N02856, N02857 |
| N02856 | C03360 | positive row contradiction | C03361 |
| N02857 | C03362 | angle(6,6235/32768) | N02858, N02863 |
| N02858 | C03363 | proxy(2,8) | N02859, N02860, N02861, N02862 |
| N02859 | C03364 | positive row contradiction | C03365 |
| N02860 | none | positive row contradiction | C03366 |
| N02861 | none | positive row contradiction | C03367 |
| N02862 | none | positive row contradiction | C03368 |
| N02863 | none | positive row contradiction | C03369 |
| N02864 | C03370 | positive row contradiction | C03371 |
| N02865 | none | positive row contradiction | C03372 |
| N02866 | C03373 | angle(6,13573/65536) | N02867, N02904 |
| N02867 | C03374 | proxy(6,8) | N02868, N02901, N02902, N02903 |
| N02868 | C03375 | proxy(5,8) | N02869, N02870, N02871, N02898 |
| N02869 | C03376 | positive row contradiction | C03377 |
| N02870 | none | positive row contradiction | C03378 |
| N02871 | C03379 | sat(2,7) | N02872, N02883, N02884, N02885, N02886, N02895, N02896, N02897 |
| N02872 | C03380 | angle(8,-14315/65536) | N02873, N02874 |
| N02873 | C03381 | positive row contradiction | C03382 |
| N02874 | C03383 | sat(4,8) | N02875, N02876, N02877, N02878, N02879, N02880, N02881, N02882 |
| N02875 | none | positive row contradiction | C03384 |
| N02876 | C03385 | positive row contradiction | C03386 |
| N02877 | none | positive row contradiction | C03387 |
| N02878 | none | positive row contradiction | C03388 |
| N02879 | none | positive row contradiction | C03389 |
| N02880 | C03390 | positive row contradiction | C03391 |
| N02881 | none | positive row contradiction | C03392 |
| N02882 | none | positive row contradiction | C03393 |
| N02883 | none | positive row contradiction | C03394 |
| N02884 | none | positive row contradiction | C03395 |
| N02885 | none | positive row contradiction | C03396 |
| N02886 | C03397 | sat(6,8) | N02887, N02888, N02889, N02890, N02891, N02892, N02893, N02894 |
| N02887 | C03398 | positive row contradiction | C03399 |
| N02888 | none | positive row contradiction | C03400 |
| N02889 | none | positive row contradiction | C03401 |
| N02890 | none | positive row contradiction | C03402 |
| N02891 | C03403 | positive row contradiction | C03404 |
| N02892 | none | positive row contradiction | C03405 |
| N02893 | C03406 | positive row contradiction | C03407 |
| N02894 | none | positive row contradiction | C03408 |
| N02895 | none | positive row contradiction | C03409 |
| N02896 | none | positive row contradiction | C03410 |
| N02897 | none | positive row contradiction | C03411 |
| N02898 | C03412 | angle(4,-1643/8192) | N02899, N02900 |
| N02899 | none | positive row contradiction | C03413 |
| N02900 | C03414 | positive row contradiction | C03415 |
| N02901 | none | positive row contradiction | C03416 |
| N02902 | none | positive row contradiction | C03417 |
| N02903 | none | positive row contradiction | C03418 |
| N02904 | C03419 | positive row contradiction | C03420 |
| N02905 | C03421 | angle(3,-13573/65536) | N02906, N02907 |
| N02906 | C03422 | positive row contradiction | C03423 |
| N02907 | C03424 | proxy(1,8) | N02908, N02909, N03022, N03033 |
| N02908 | none | positive row contradiction | C03425 |
| N02909 | C03426 | angle(6,13573/65536) | N02910, N03021 |
| N02910 | C03427 | angle(4,13573/65536) | N02911, N03020 |
| N02911 | C03428 | proxy(5,8) | N02912, N02913, N02922, N03019 |
| N02912 | none | positive row contradiction | C03429 |
| N02913 | C03430 | angle(8,-13573/65536) | N02914, N02917 |
| N02914 | C03431 | angle(7,13573/65536) | N02915, N02916 |
| N02915 | C03432 | positive row contradiction | C03433 |
| N02916 | C03434 | positive row contradiction | C03435 |
| N02917 | C03436 | proxy(6,8) | N02918, N02919, N02920, N02921 |
| N02918 | none | positive row contradiction | C03437 |
| N02919 | none | positive row contradiction | C03438 |
| N02920 | C03439 | positive row contradiction | C03440 |
| N02921 | none | positive row contradiction | C03441 |
| N02922 | C03442 | sat(2,8) | N02923, N02924, N02925, N02926, N02963, N02964, N02965, N02966 |
| N02923 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N02924 | none | positive row contradiction | C03443 |
| N02925 | none | positive row contradiction | C03444 |
| N02926 | C03445 | sat(0,4) | N02927, N02928, N02929, N02930, N02941, N02942, N02943, N02944 |
| N02927 | none | positive row contradiction | C03446 |
| N02928 | none | positive row contradiction | C03447 |
| N02929 | none | positive row contradiction | C03448 |
| N02930 | C03449 | proxy(1,4) | N02931, N02932, N02933, N02934 |
| N02931 | none | positive row contradiction | C03450 |
| N02932 | none | positive row contradiction | C03451 |
| N02933 | none | positive row contradiction | C03452 |
| N02934 | C03453 | angle(8,-12903/65536) | N02935, N02936 |
| N02935 | none | positive row contradiction | C03454 |
| N02936 | C03455 | angle(8,-11893/131072) | N02937, N02938 |
| N02937 | C03456 | positive row contradiction | C03457 |
| N02938 | C03458 | angle(8,-11893/262144) | N02939, N02940 |
| N02939 | C03459 | positive row contradiction | C03460 |
| N02940 | C03461 | uniform sharp terminal | C03462 |
| N02941 | none | positive row contradiction | C03463 |
| N02942 | none | positive row contradiction | C03464 |
| N02943 | none | positive row contradiction | C03465 |
| N02944 | C03466 | proxy(1,4) | N02945, N02946, N02947, N02948 |
| N02945 | none | positive row contradiction | C03467 |
| N02946 | none | positive row contradiction | C03468 |
| N02947 | none | positive row contradiction | C03469 |
| N02948 | C03470 | sat(6,8) | N02949, N02950, N02951, N02952, N02953, N02954, N02955, N02962 |
| N02949 | none | positive row contradiction | C03471 |
| N02950 | none | positive row contradiction | C03472 |
| N02951 | C03473 | uniform sharp terminal | C03474 |
| N02952 | none | positive row contradiction | C03475 |
| N02953 | none | positive row contradiction | C03476 |
| N02954 | none | positive row contradiction | C03477 |
| N02955 | C03478 | angle(7,13573/65536) | N02956, N02959 |
| N02956 | C03479 | angle(8,-5069/131072) | N02957, N02958 |
| N02957 | none | positive row contradiction | C03480 |
| N02958 | C03481 | uniform sharp terminal from box | C03481 |
| N02959 | C03482 | angle(8,-5069/131072) | N02960, N02961 |
| N02960 | none | positive row contradiction | C03483 |
| N02961 | C03484 | uniform sharp terminal from box | C03484 |
| N02962 | none | positive row contradiction | C03485 |
| N02963 | C03486 | positive row contradiction | C03487 |
| N02964 | none | positive row contradiction | C03488 |
| N02965 | none | positive row contradiction | C03489 |
| N02966 | C03490 | sat(2,7) | N02967, N02994, N02995, N02996, N02997, N03016, N03017, N03018 |
| N02967 | C03491 | angle(7,13573/65536) | N02968, N02981 |
| N02968 | C03492 | angle(8,-19589/131072) | N02969, N02970 |
| N02969 | C03493 | positive row contradiction | C03494 |
| N02970 | C03495 | proxy(1,4) | N02971, N02972, N02973, N02974 |
| N02971 | none | positive row contradiction | C03496 |
| N02972 | none | positive row contradiction | C03497 |
| N02973 | none | positive row contradiction | C03498 |
| N02974 | C03499 | angle(8,-8349/131072) | N02975, N02976 |
| N02975 | C03500 | positive row contradiction | C03501 |
| N02976 | C03502 | angle(8,-8349/262144) | N02977, N02980 |
| N02977 | C03503 | angle(8,-24377/524288) | N02978, N02979 |
| N02978 | none | positive row contradiction | C03504 |
| N02979 | C03505 | uniform sharp terminal from box | C03505 |
| N02980 | C03506 | uniform sharp terminal | C03507 |
| N02981 | C03508 | sat(6,8) | N02982, N02983, N02984, N02987, N02988, N02989, N02990, N02993 |
| N02982 | none | positive row contradiction | C03509 |
| N02983 | none | positive row contradiction | C03510 |
| N02984 | C03511 | angle(4,2197/65536) | N02985, N02986 |
| N02985 | C03512 | uniform sharp terminal | C03513 |
| N02986 | none | positive row contradiction | C03514 |
| N02987 | none | positive row contradiction | C03515 |
| N02988 | none | positive row contradiction | C03516 |
| N02989 | none | positive row contradiction | C03517 |
| N02990 | C03518 | angle(8,-795/8192) | N02991, N02992 |
| N02991 | none | positive row contradiction | C03519 |
| N02992 | C03520 | uniform sharp terminal | C03521 |
| N02993 | none | positive row contradiction | C03522 |
| N02994 | none | positive row contradiction | C03523 |
| N02995 | none | positive row contradiction | C03524 |
| N02996 | none | positive row contradiction | C03525 |
| N02997 | C03526 | proxy(3,8) | N02998, N03013, N03014, N03015 |
| N02998 | C03527 | angle(8,-19589/131072) | N02999, N03000 |
| N02999 | none | positive row contradiction | C03528 |
| N03000 | C03529 | sat(6,8) | N03001, N03002, N03003, N03006, N03007, N03008, N03009, N03012 |
| N03001 | none | positive row contradiction | C03530 |
| N03002 | none | positive row contradiction | C03531 |
| N03003 | C03532 | angle(7,25539/131072) | N03004, N03005 |
| N03004 | C03533 | uniform sharp terminal | C03534 |
| N03005 | C03535 | uniform sharp terminal | C03536 |
| N03006 | none | positive row contradiction | C03537 |
| N03007 | none | positive row contradiction | C03538 |
| N03008 | none | positive row contradiction | C03539 |
| N03009 | C03540 | angle(8,-2443/65536) | N03010, N03011 |
| N03010 | none | positive row contradiction | C03541 |
| N03011 | C03542 | uniform sharp terminal | C03543 |
| N03012 | none | positive row contradiction | C03544 |
| N03013 | none | positive row contradiction | C03545 |
| N03014 | none | positive row contradiction | C03546 |
| N03015 | none | positive row contradiction | C03547 |
| N03016 | none | positive row contradiction | C03548 |
| N03017 | none | positive row contradiction | C03549 |
| N03018 | C03550 | positive row contradiction | C03551 |
| N03019 | C03552 | positive row contradiction | C03553 |
| N03020 | C03554 | positive row contradiction | C03555 |
| N03021 | C03556 | positive row contradiction | C03557 |
| N03022 | C03558 | proxy(7,8) | N03023, N03024, N03031, N03032 |
| N03023 | none | positive row contradiction | C03559 |
| N03024 | C03560 | proxy(2,8) | N03025, N03028, N03029, N03030 |
| N03025 | C03561 | angle(4,13573/65536) | N03026, N03027 |
| N03026 | C03562 | positive row contradiction | C03563 |
| N03027 | none | positive row contradiction | C03564 |
| N03028 | none | positive row contradiction | C03565 |
| N03029 | none | positive row contradiction | C03566 |
| N03030 | none | positive row contradiction | C03567 |
| N03031 | C03568 | positive row contradiction | C03569 |
| N03032 | none | positive row contradiction | C03570 |
| N03033 | C03571 | proxy(6,8) | N03034, N03069, N03070, N03071 |
| N03034 | C03572 | angle(6,13573/65536) | N03035, N03068 |
| N03035 | C03573 | proxy(5,8) | N03036, N03037, N03038, N03065 |
| N03036 | C03574 | positive row contradiction | C03575 |
| N03037 | none | positive row contradiction | C03576 |
| N03038 | C03577 | angle(7,13573/65536) | N03039, N03064 |
| N03039 | C03578 | sat(6,8) | N03040, N03049, N03050, N03051, N03052, N03061, N03062, N03063 |
| N03040 | C03579 | sat(4,8) | N03041, N03042, N03043, N03044, N03045, N03046, N03047, N03048 |
| N03041 | none | positive row contradiction | C03580 |
| N03042 | none | positive row contradiction | C03581 |
| N03043 | none | positive row contradiction | C03582 |
| N03044 | none | positive row contradiction | C03583 |
| N03045 | none | positive row contradiction | C03584 |
| N03046 | none | positive row contradiction | C03585 |
| N03047 | none | positive row contradiction | C03586 |
| N03048 | none | positive row contradiction | C03587 |
| N03049 | none | positive row contradiction | C03588 |
| N03050 | none | positive row contradiction | C03589 |
| N03051 | none | positive row contradiction | C03590 |
| N03052 | C03591 | sat(4,8) | N03053, N03054, N03055, N03056, N03057, N03058, N03059, N03060 |
| N03053 | none | positive row contradiction | C03592 |
| N03054 | none | positive row contradiction | C03593 |
| N03055 | none | positive row contradiction | C03594 |
| N03056 | none | positive row contradiction | C03595 |
| N03057 | none | positive row contradiction | C03596 |
| N03058 | none | positive row contradiction | C03597 |
| N03059 | none | positive row contradiction | C03598 |
| N03060 | none | positive row contradiction | C03599 |
| N03061 | none | positive row contradiction | C03600 |
| N03062 | C03601 | positive row contradiction | C03602 |
| N03063 | none | positive row contradiction | C03603 |
| N03064 | C03604 | positive row contradiction | C03605 |
| N03065 | C03606 | angle(8,-13573/65536) | N03066, N03067 |
| N03066 | none | positive row contradiction | C03607 |
| N03067 | C03608 | positive row contradiction | C03609 |
| N03068 | C03610 | positive row contradiction | C03611 |
| N03069 | none | positive row contradiction | C03612 |
| N03070 | none | positive row contradiction | C03613 |
| N03071 | C03614 | positive row contradiction | C03615 |
| N03072 | C03616 | angle(4,0) | N03073, N03190 |
| N03073 | C03617 | angle(3,-13573/65536) | N03074, N03075 |
| N03074 | C03618 | positive row contradiction | C03619 |
| N03075 | C03620 | proxy(1,8) | N03076, N03077, N03152, N03165 |
| N03076 | none | positive row contradiction | C03621 |
| N03077 | C03622 | angle(4,-13573/65536) | N03078, N03081 |
| N03078 | C03623 | angle(6,13573/65536) | N03079, N03080 |
| N03079 | C03624 | positive row contradiction | C03625 |
| N03080 | none | positive row contradiction | C03626 |
| N03081 | C03627 | angle(6,13573/65536) | N03082, N03151 |
| N03082 | C03628 | proxy(5,8) | N03083, N03084, N03093, N03150 |
| N03083 | none | positive row contradiction | C03629 |
| N03084 | C03630 | proxy(6,8) | N03085, N03086, N03087, N03092 |
| N03085 | none | positive row contradiction | C03631 |
| N03086 | none | positive row contradiction | C03632 |
| N03087 | C03633 | proxy(3,8) | N03088, N03089, N03090, N03091 |
| N03088 | none | positive row contradiction | C03634 |
| N03089 | none | positive row contradiction | C03635 |
| N03090 | none | positive row contradiction | C03636 |
| N03091 | none | positive row contradiction | C03637 |
| N03092 | none | positive row contradiction | C03638 |
| N03093 | C03639 | sat(2,8) | N03094, N03095, N03096, N03097, N03116, N03117, N03122, N03123 |
| N03094 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N03095 | none | positive row contradiction | C03640 |
| N03096 | none | positive row contradiction | C03641 |
| N03097 | C03642 | proxy(3,8) | N03098, N03113, N03114, N03115 |
| N03098 | C03643 | angle(8,13573/65536) | N03099, N03112 |
| N03099 | C03644 | sat(6,8) | N03100, N03101, N03102, N03105, N03106, N03107, N03108, N03111 |
| N03100 | none | positive row contradiction | C03645 |
| N03101 | none | positive row contradiction | C03646 |
| N03102 | C03647 | angle(4,-5887/131072) | N03103, N03104 |
| N03103 | C03648 | positive row contradiction | C03649 |
| N03104 | C03650 | uniform sharp terminal | C03651 |
| N03105 | none | positive row contradiction | C03652 |
| N03106 | none | positive row contradiction | C03653 |
| N03107 | none | positive row contradiction | C03654 |
| N03108 | C03655 | angle(4,-5887/131072) | N03109, N03110 |
| N03109 | C03656 | positive row contradiction | C03657 |
| N03110 | C03658 | uniform sharp terminal | C03659 |
| N03111 | none | positive row contradiction | C03660 |
| N03112 | C03661 | positive row contradiction | C03662 |
| N03113 | none | positive row contradiction | C03663 |
| N03114 | none | positive row contradiction | C03664 |
| N03115 | none | positive row contradiction | C03665 |
| N03116 | none | positive row contradiction | C03666 |
| N03117 | C03667 | proxy(6,8) | N03118, N03119, N03120, N03121 |
| N03118 | none | positive row contradiction | C03668 |
| N03119 | none | positive row contradiction | C03669 |
| N03120 | C03670 | positive row contradiction | C03671 |
| N03121 | none | positive row contradiction | C03672 |
| N03122 | none | positive row contradiction | C03673 |
| N03123 | C03674 | angle(8,13573/65536) | N03124, N03149 |
| N03124 | C03675 | angle(7,13573/65536) | N03125, N03136 |
| N03125 | C03676 | angle(8,13573/131072) | N03126, N03135 |
| N03126 | C03677 | angle(8,13573/262144) | N03127, N03134 |
| N03127 | C03678 | proxy(1,4) | N03128, N03129, N03130, N03131 |
| N03128 | none | positive row contradiction | C03679 |
| N03129 | none | positive row contradiction | C03680 |
| N03130 | none | positive row contradiction | C03681 |
| N03131 | C03682 | angle(4,-2477/65536) | N03132, N03133 |
| N03132 | C03683 | positive row contradiction | C03684 |
| N03133 | C03685 | uniform sharp terminal | C03686 |
| N03134 | C03687 | positive row contradiction | C03688 |
| N03135 | C03689 | positive row contradiction | C03690 |
| N03136 | C03691 | angle(8,13573/131072) | N03137, N03148 |
| N03137 | C03692 | sat(1,7) | N03138, N03139, N03140, N03143, N03144, N03145, N03146, N03147 |
| N03138 | none | positive row contradiction | C03693 |
| N03139 | none | positive row contradiction | C03694 |
| N03140 | C03695 | angle(4,-5979/131072) | N03141, N03142 |
| N03141 | C03696 | positive row contradiction | C03697 |
| N03142 | C03698 | uniform sharp terminal | C03699 |
| N03143 | none | positive row contradiction | C03700 |
| N03144 | none | positive row contradiction | C03701 |
| N03145 | none | positive row contradiction | C03702 |
| N03146 | C03703 | positive row contradiction | C03704 |
| N03147 | none | positive row contradiction | C03705 |
| N03148 | C03706 | positive row contradiction | C03707 |
| N03149 | C03708 | positive row contradiction | C03709 |
| N03150 | C03710 | positive row contradiction | C03711 |
| N03151 | C03712 | positive row contradiction | C03713 |
| N03152 | C03714 | angle(6,13573/65536) | N03153, N03164 |
| N03153 | C03715 | proxy(2,8) | N03154, N03161, N03162, N03163 |
| N03154 | C03716 | angle(4,-13573/65536) | N03155, N03156 |
| N03155 | none | positive row contradiction | C03717 |
| N03156 | C03718 | proxy(7,8) | N03157, N03158, N03159, N03160 |
| N03157 | none | positive row contradiction | C03719 |
| N03158 | C03720 | positive row contradiction | C03721 |
| N03159 | none | positive row contradiction | C03722 |
| N03160 | none | positive row contradiction | C03723 |
| N03161 | none | positive row contradiction | C03724 |
| N03162 | none | positive row contradiction | C03725 |
| N03163 | none | positive row contradiction | C03726 |
| N03164 | C03727 | positive row contradiction | C03728 |
| N03165 | C03729 | proxy(5,8) | N03166, N03167, N03168, N03185 |
| N03166 | C03730 | positive row contradiction | C03731 |
| N03167 | C03732 | positive row contradiction | C03733 |
| N03168 | C03734 | angle(6,13573/65536) | N03169, N03184 |
| N03169 | C03735 | sat(5,8) | N03170, N03171, N03172, N03173, N03174, N03175, N03176, N03183 |
| N03170 | none | positive row contradiction | C03736 |
| N03171 | C03737 | positive row contradiction | C03738 |
| N03172 | C03739 | positive row contradiction | C03740 |
| N03173 | none | positive row contradiction | C03741 |
| N03174 | C03742 | positive row contradiction | C03743 |
| N03175 | C03744 | positive row contradiction | C03745 |
| N03176 | C03746 | proxy(6,8) | N03177, N03180, N03181, N03182 |
| N03177 | C03747 | angle(4,-22293/131072) | N03178, N03179 |
| N03178 | none | positive row contradiction | C03748 |
| N03179 | C03749 | positive row contradiction | C03750 |
| N03180 | none | positive row contradiction | C03751 |
| N03181 | none | positive row contradiction | C03752 |
| N03182 | none | positive row contradiction | C03753 |
| N03183 | none | positive row contradiction | C03754 |
| N03184 | C03755 | positive row contradiction | C03756 |
| N03185 | C03757 | angle(7,13573/65536) | N03186, N03189 |
| N03186 | C03758 | angle(8,13573/65536) | N03187, N03188 |
| N03187 | C03759 | positive row contradiction | C03760 |
| N03188 | none | positive row contradiction | C03761 |
| N03189 | none | positive row contradiction | C03762 |
| N03190 | C03763 | angle(3,-13573/65536) | N03191, N03192 |
| N03191 | C03764 | positive row contradiction | C03765 |
| N03192 | C03766 | angle(2,20839/131072) | N03193, N03278 |
| N03193 | C03767 | angle(6,13573/65536) | N03194, N03277 |
| N03194 | C03768 | proxy(1,8) | N03195, N03196, N03247, N03258 |
| N03195 | none | positive row contradiction | C03769 |
| N03196 | C03770 | proxy(5,8) | N03197, N03198, N03203, N03246 |
| N03197 | none | positive row contradiction | C03771 |
| N03198 | C03772 | proxy(3,8) | N03199, N03200, N03201, N03202 |
| N03199 | none | positive row contradiction | C03773 |
| N03200 | none | positive row contradiction | C03774 |
| N03201 | C03775 | positive row contradiction | C03776 |
| N03202 | C03777 | positive row contradiction | C03778 |
| N03203 | C03779 | angle(8,13573/65536) | N03204, N03239 |
| N03204 | C03780 | proxy(2,8) | N03205, N03206, N03207, N03208 |
| N03205 | none | positive row contradiction | C03781 |
| N03206 | none | positive row contradiction | C03782 |
| N03207 | none | positive row contradiction | C03783 |
| N03208 | C03784 | angle(7,13573/65536) | N03209, N03216 |
| N03209 | C03785 | angle(8,13573/131072) | N03210, N03215 |
| N03210 | C03786 | angle(8,13573/262144) | N03211, N03214 |
| N03211 | C03787 | angle(8,13573/524288) | N03212, N03213 |
| N03212 | C03788 | uniform sharp terminal | C03789 |
| N03213 | C03790 | positive row contradiction | C03791 |
| N03214 | C03792 | positive row contradiction | C03793 |
| N03215 | C03794 | positive row contradiction | C03795 |
| N03216 | C03796 | sat(2,7) | N03217, N03228, N03229, N03230, N03231, N03236, N03237, N03238 |
| N03217 | C03797 | angle(8,12027/131072) | N03218, N03227 |
| N03218 | C03798 | sat(1,7) | N03219, N03220, N03221, N03222, N03223, N03224, N03225, N03226 |
| N03219 | none | positive row contradiction | C03799 |
| N03220 | none | positive row contradiction | C03800 |
| N03221 | C03801 | uniform sharp terminal | C03802 |
| N03222 | none | positive row contradiction | C03803 |
| N03223 | none | positive row contradiction | C03804 |
| N03224 | none | positive row contradiction | C03805 |
| N03225 | none | positive row contradiction | C03806 |
| N03226 | none | positive row contradiction | C03807 |
| N03227 | none | positive row contradiction | C03808 |
| N03228 | none | positive row contradiction | C03809 |
| N03229 | none | positive row contradiction | C03810 |
| N03230 | none | positive row contradiction | C03811 |
| N03231 | C03812 | angle(8,12003/131072) | N03232, N03235 |
| N03232 | C03813 | angle(8,4845/131072) | N03233, N03234 |
| N03233 | C03814 | uniform sharp terminal | C03815 |
| N03234 | none | positive row contradiction | C03816 |
| N03235 | none | positive row contradiction | C03817 |
| N03236 | none | positive row contradiction | C03818 |
| N03237 | none | positive row contradiction | C03819 |
| N03238 | C03820 | positive row contradiction | C03821 |
| N03239 | C03822 | proxy(2,8) | N03240, N03241, N03242, N03243 |
| N03240 | none | positive row contradiction | C03823 |
| N03241 | none | positive row contradiction | C03824 |
| N03242 | none | positive row contradiction | C03825 |
| N03243 | C03826 | angle(7,13573/65536) | N03244, N03245 |
| N03244 | C03827 | positive row contradiction | C03828 |
| N03245 | C03829 | positive row contradiction | C03830 |
| N03246 | none | positive row contradiction | C03831 |
| N03247 | C03832 | proxy(2,8) | N03248, N03255, N03256, N03257 |
| N03248 | C03833 | angle(8,13573/65536) | N03249, N03254 |
| N03249 | C03834 | proxy(7,8) | N03250, N03251, N03252, N03253 |
| N03250 | none | positive row contradiction | C03835 |
| N03251 | none | positive row contradiction | C03836 |
| N03252 | none | positive row contradiction | C03837 |
| N03253 | none | positive row contradiction | C03838 |
| N03254 | C03839 | positive row contradiction | C03840 |
| N03255 | none | positive row contradiction | C03841 |
| N03256 | none | positive row contradiction | C03842 |
| N03257 | none | positive row contradiction | C03843 |
| N03258 | C03844 | proxy(5,8) | N03259, N03260, N03261, N03276 |
| N03259 | C03845 | positive row contradiction | C03846 |
| N03260 | C03847 | positive row contradiction | C03848 |
| N03261 | C03849 | sat(5,8) | N03262, N03263, N03264, N03265, N03266, N03267, N03268, N03275 |
| N03262 | none | positive row contradiction | C03850 |
| N03263 | none | positive row contradiction | C03851 |
| N03264 | C03852 | positive row contradiction | C03853 |
| N03265 | none | positive row contradiction | C03854 |
| N03266 | C03855 | positive row contradiction | C03856 |
| N03267 | none | positive row contradiction | C03857 |
| N03268 | C03858 | angle(7,13573/65536) | N03269, N03274 |
| N03269 | C03859 | proxy(6,8) | N03270, N03271, N03272, N03273 |
| N03270 | C03860 | positive row contradiction | C03861 |
| N03271 | none | positive row contradiction | C03862 |
| N03272 | none | positive row contradiction | C03863 |
| N03273 | none | positive row contradiction | C03864 |
| N03274 | C03865 | positive row contradiction | C03866 |
| N03275 | none | positive row contradiction | C03867 |
| N03276 | C03868 | positive row contradiction | C03869 |
| N03277 | C03870 | positive row contradiction | C03871 |
| N03278 | C03872 | positive row contradiction | C03873 |
| N03279 | none | angle(4,0) | N03280, N03611 |
| N03280 | C03874 | angle(3,-13573/65536) | N03281, N03282 |
| N03281 | C03875 | positive row contradiction | C03876 |
| N03282 | C03877 | angle(8,0) | N03283, N03396 |
| N03283 | C03878 | proxy(1,8) | N03284, N03285, N03360, N03369 |
| N03284 | none | positive row contradiction | C03879 |
| N03285 | C03880 | proxy(5,8) | N03286, N03287, N03294, N03357 |
| N03286 | none | positive row contradiction | C03881 |
| N03287 | C03882 | proxy(2,8) | N03288, N03289, N03290, N03291 |
| N03288 | none | positive row contradiction | C03883 |
| N03289 | none | positive row contradiction | C03884 |
| N03290 | none | positive row contradiction | C03885 |
| N03291 | C03886 | angle(6,10669/65536) | N03292, N03293 |
| N03292 | C03887 | positive row contradiction | C03888 |
| N03293 | none | positive row contradiction | C03889 |
| N03294 | C03890 | angle(6,6235/32768) | N03295, N03356 |
| N03295 | C03891 | angle(4,-26295/131072) | N03296, N03297 |
| N03296 | none | positive row contradiction | C03892 |
| N03297 | C03893 | proxy(2,8) | N03298, N03299, N03300, N03301 |
| N03298 | none | positive row contradiction | C03894 |
| N03299 | none | positive row contradiction | C03895 |
| N03300 | none | positive row contradiction | C03896 |
| N03301 | C03897 | angle(8,-13573/65536) | N03302, N03303 |
| N03302 | C03898 | positive row contradiction | C03899 |
| N03303 | C03900 | sat(5,8) | N03304, N03305, N03306, N03335, N03336, N03337, N03338, N03355 |
| N03304 | none | positive row contradiction | C03901 |
| N03305 | none | positive row contradiction | C03902 |
| N03306 | C03903 | angle(8,-13573/131072) | N03307, N03308 |
| N03307 | C03904 | positive row contradiction | C03905 |
| N03308 | C03906 | sat(1,4) | N03309, N03310, N03311, N03312, N03321, N03322, N03323, N03324 |
| N03309 | none | positive row contradiction | C03907 |
| N03310 | none | positive row contradiction | C03908 |
| N03311 | none | positive row contradiction | C03909 |
| N03312 | C03910 | angle(8,-13573/262144) | N03313, N03314 |
| N03313 | C03911 | positive row contradiction | C03912 |
| N03314 | C03913 | angle(4,-4243/131072) | N03315, N03316 |
| N03315 | C03914 | positive row contradiction | C03915 |
| N03316 | C03916 | angle(8,-13573/524288) | N03317, N03320 |
| N03317 | C03917 | angle(4,-4243/262144) | N03318, N03319 |
| N03318 | C03918 | positive row contradiction | C03919 |
| N03319 | C03920 | positive row contradiction | C03921 |
| N03320 | C03922 | uniform sharp terminal | C03923 |
| N03321 | none | positive row contradiction | C03924 |
| N03322 | none | positive row contradiction | C03925 |
| N03323 | none | positive row contradiction | C03926 |
| N03324 | C03927 | angle(7,13573/65536) | N03325, N03330 |
| N03325 | C03928 | angle(8,-6257/131072) | N03326, N03327 |
| N03326 | C03929 | positive row contradiction | C03930 |
| N03327 | C03931 | angle(4,-3671/131072) | N03328, N03329 |
| N03328 | C03932 | positive row contradiction | C03933 |
| N03329 | C03934 | uniform sharp terminal | C03935 |
| N03330 | C03936 | angle(8,-3051/65536) | N03331, N03332 |
| N03331 | C03937 | positive row contradiction | C03938 |
| N03332 | C03939 | angle(4,-3651/131072) | N03333, N03334 |
| N03333 | C03940 | positive row contradiction | C03941 |
| N03334 | C03942 | uniform sharp terminal | C03943 |
| N03335 | none | positive row contradiction | C03944 |
| N03336 | none | positive row contradiction | C03945 |
| N03337 | none | positive row contradiction | C03946 |
| N03338 | C03947 | angle(8,-13573/131072) | N03339, N03340 |
| N03339 | C03948 | positive row contradiction | C03949 |
| N03340 | C03950 | angle(8,-13573/262144) | N03341, N03344 |
| N03341 | C03951 | angle(4,-4949/131072) | N03342, N03343 |
| N03342 | C03952 | positive row contradiction | C03953 |
| N03343 | C03954 | positive row contradiction | C03955 |
| N03344 | C03956 | angle(4,-4949/131072) | N03345, N03346 |
| N03345 | C03957 | positive row contradiction | C03958 |
| N03346 | C03959 | angle(8,-13573/524288) | N03347, N03354 |
| N03347 | C03960 | angle(4,-4949/262144) | N03348, N03351 |
| N03348 | C03961 | angle(8,-40125/1048576) | N03349, N03350 |
| N03349 | none | positive row contradiction | C03962 |
| N03350 | C03963 | uniform sharp terminal from box | C03963 |
| N03351 | C03964 | angle(8,-40125/1048576) | N03352, N03353 |
| N03352 | none | positive row contradiction | C03965 |
| N03353 | C03966 | uniform sharp terminal from box | C03966 |
| N03354 | C03967 | uniform sharp terminal | C03968 |
| N03355 | none | positive row contradiction | C03969 |
| N03356 | none | positive row contradiction | C03970 |
| N03357 | C03971 | angle(8,-14797/65536) | N03358, N03359 |
| N03358 | none | positive row contradiction | C03972 |
| N03359 | none | positive row contradiction | C03973 |
| N03360 | C03974 | proxy(7,8) | N03361, N03362, N03367, N03368 |
| N03361 | none | positive row contradiction | C03975 |
| N03362 | C03976 | proxy(2,8) | N03363, N03364, N03365, N03366 |
| N03363 | C03977 | positive row contradiction | C03978 |
| N03364 | none | positive row contradiction | C03979 |
| N03365 | none | positive row contradiction | C03980 |
| N03366 | none | positive row contradiction | C03981 |
| N03367 | none | positive row contradiction | C03982 |
| N03368 | none | positive row contradiction | C03983 |
| N03369 | C03984 | proxy(6,8) | N03370, N03393, N03394, N03395 |
| N03370 | C03985 | angle(6,6235/32768) | N03371, N03392 |
| N03371 | C03986 | proxy(5,8) | N03372, N03373, N03374, N03391 |
| N03372 | C03987 | positive row contradiction | C03988 |
| N03373 | none | positive row contradiction | C03989 |
| N03374 | C03990 | sat(5,8) | N03375, N03376, N03377, N03378, N03379, N03380, N03381, N03390 |
| N03375 | none | positive row contradiction | C03991 |
| N03376 | none | positive row contradiction | C03992 |
| N03377 | C03993 | positive row contradiction | C03994 |
| N03378 | none | positive row contradiction | C03995 |
| N03379 | none | positive row contradiction | C03996 |
| N03380 | none | positive row contradiction | C03997 |
| N03381 | C03998 | sat(4,8) | N03382, N03383, N03384, N03385, N03386, N03387, N03388, N03389 |
| N03382 | none | positive row contradiction | C03999 |
| N03383 | C04000 | positive row contradiction | C04001 |
| N03384 | none | positive row contradiction | C04002 |
| N03385 | none | positive row contradiction | C04003 |
| N03386 | none | positive row contradiction | C04004 |
| N03387 | C04005 | positive row contradiction | C04006 |
| N03388 | none | positive row contradiction | C04007 |
| N03389 | none | common-axis chain [[8,1],[4,8,5]] | endpoint squared distance < 4 |
| N03390 | none | positive row contradiction | C04008 |
| N03391 | C04009 | positive row contradiction | C04010 |
| N03392 | none | positive row contradiction | C04011 |
| N03393 | none | positive row contradiction | C04012 |
| N03394 | none | positive row contradiction | C04013 |
| N03395 | none | positive row contradiction | C04014 |
| N03396 | C04015 | proxy(1,8) | N03397, N03398, N03567, N03582 |
| N03397 | none | positive row contradiction | C04016 |
| N03398 | C04017 | angle(7,13573/65536) | N03399, N03486 |
| N03399 | C04018 | sat(1,8) | N03400, N03401, N03418, N03419, N03424, N03425, N03478, N03483 |
| N03400 | none | positive row contradiction | C04019 |
| N03401 | C04020 | angle(6,10669/65536) | N03402, N03417 |
| N03402 | C04021 | angle(4,-22705/131072) | N03403, N03404 |
| N03403 | none | positive row contradiction | C04022 |
| N03404 | C04023 | proxy(6,8) | N03405, N03406, N03407, N03416 |
| N03405 | none | positive row contradiction | C04024 |
| N03406 | none | positive row contradiction | C04025 |
| N03407 | C04026 | proxy(2,8) | N03408, N03409, N03410, N03411 |
| N03408 | none | positive row contradiction | C04027 |
| N03409 | none | positive row contradiction | C04028 |
| N03410 | none | positive row contradiction | C04029 |
| N03411 | C04030 | angle(8,20263/131072) | N03412, N03415 |
| N03412 | C04031 | angle(4,-6411/131072) | N03413, N03414 |
| N03413 | C04032 | positive row contradiction | C04033 |
| N03414 | C04034 | uniform sharp terminal | C04035 |
| N03415 | none | positive row contradiction | C04036 |
| N03416 | none | positive row contradiction | C04037 |
| N03417 | none | positive row contradiction | C04038 |
| N03418 | C04039 | positive row contradiction | C04040 |
| N03419 | C04041 | proxy(5,8) | N03420, N03421, N03422, N03423 |
| N03420 | none | positive row contradiction | C04042 |
| N03421 | none | positive row contradiction | C04043 |
| N03422 | none | positive row contradiction | C04044 |
| N03423 | none | positive row contradiction | C04045 |
| N03424 | none | positive row contradiction | C04046 |
| N03425 | C04047 | angle(8,13573/65536) | N03426, N03465 |
| N03426 | C04048 | proxy(5,8) | N03427, N03428, N03433, N03464 |
| N03427 | none | positive row contradiction | C04049 |
| N03428 | C04050 | proxy(6,8) | N03429, N03430, N03431, N03432 |
| N03429 | none | positive row contradiction | C04051 |
| N03430 | none | positive row contradiction | C04052 |
| N03431 | C04053 | positive row contradiction | C04054 |
| N03432 | none | positive row contradiction | C04055 |
| N03433 | C04056 | proxy(2,8) | N03434, N03435, N03436, N03437 |
| N03434 | none | positive row contradiction | C04057 |
| N03435 | none | positive row contradiction | C04058 |
| N03436 | none | positive row contradiction | C04059 |
| N03437 | C04060 | sat(1,4) | N03438, N03439, N03440, N03441, N03450, N03451, N03452, N03453 |
| N03438 | none | positive row contradiction | C04061 |
| N03439 | none | positive row contradiction | C04062 |
| N03440 | none | positive row contradiction | C04063 |
| N03441 | C04064 | proxy(6,8) | N03442, N03443, N03444, N03449 |
| N03442 | none | positive row contradiction | C04065 |
| N03443 | none | positive row contradiction | C04066 |
| N03444 | C04067 | angle(8,11725/131072) | N03445, N03448 |
| N03445 | C04068 | angle(4,-6143/131072) | N03446, N03447 |
| N03446 | C04069 | positive row contradiction | C04070 |
| N03447 | C04071 | uniform sharp terminal | C04072 |
| N03448 | none | positive row contradiction | C04073 |
| N03449 | none | positive row contradiction | C04074 |
| N03450 | none | positive row contradiction | C04075 |
| N03451 | none | positive row contradiction | C04076 |
| N03452 | none | positive row contradiction | C04077 |
| N03453 | C04078 | angle(8,13573/131072) | N03454, N03463 |
| N03454 | C04079 | angle(4,-7035/131072) | N03455, N03456 |
| N03455 | C04080 | positive row contradiction | C04081 |
| N03456 | C04082 | angle(8,2825/65536) | N03457, N03462 |
| N03457 | C04083 | angle(4,-7035/262144) | N03458, N03461 |
| N03458 | C04084 | angle(6,2341/131072) | N03459, N03460 |
| N03459 | C04085 | positive row contradiction | C04086 |
| N03460 | C04087 | uniform sharp terminal from box | C04087 |
| N03461 | C04088 | uniform sharp terminal | C04089 |
| N03462 | none | positive row contradiction | C04090 |
| N03463 | C04091 | positive row contradiction | C04092 |
| N03464 | none | positive row contradiction | C04093 |
| N03465 | C04094 | proxy(5,8) | N03466, N03467, N03472, N03477 |
| N03466 | none | positive row contradiction | C04095 |
| N03467 | C04096 | proxy(6,8) | N03468, N03469, N03470, N03471 |
| N03468 | none | positive row contradiction | C04097 |
| N03469 | none | positive row contradiction | C04098 |
| N03470 | C04099 | positive row contradiction | C04100 |
| N03471 | none | positive row contradiction | C04101 |
| N03472 | C04102 | proxy(6,8) | N03473, N03474, N03475, N03476 |
| N03473 | none | positive row contradiction | C04103 |
| N03474 | none | positive row contradiction | C04104 |
| N03475 | C04105 | positive row contradiction | C04106 |
| N03476 | none | positive row contradiction | C04107 |
| N03477 | none | positive row contradiction | C04108 |
| N03478 | C04109 | angle(6,10669/65536) | N03479, N03482 |
| N03479 | C04110 | angle(8,13573/65536) | N03480, N03481 |
| N03480 | C04111 | positive row contradiction | C04112 |
| N03481 | none | positive row contradiction | C04113 |
| N03482 | none | positive row contradiction | C04114 |
| N03483 | C04115 | angle(4,-26295/131072) | N03484, N03485 |
| N03484 | none | positive row contradiction | C04116 |
| N03485 | C04117 | positive row contradiction | C04118 |
| N03486 | C04119 | sat(1,8) | N03487, N03488, N03527, N03528, N03531, N03532, N03559, N03564 |
| N03487 | none | positive row contradiction | C04120 |
| N03488 | C04121 | angle(4,-26295/131072) | N03489, N03490 |
| N03489 | none | positive row contradiction | C04122 |
| N03490 | C04123 | angle(8,13573/65536) | N03491, N03522 |
| N03491 | C04124 | proxy(6,8) | N03492, N03493, N03494, N03521 |
| N03492 | none | positive row contradiction | C04125 |
| N03493 | none | positive row contradiction | C04126 |
| N03494 | C04127 | sat(1,4) | N03495, N03496, N03497, N03498, N03503, N03504, N03505, N03506 |
| N03495 | none | positive row contradiction | C04128 |
| N03496 | none | positive row contradiction | C04129 |
| N03497 | none | positive row contradiction | C04130 |
| N03498 | C04131 | angle(8,6437/65536) | N03499, N03502 |
| N03499 | C04132 | angle(4,-6541/131072) | N03500, N03501 |
| N03500 | C04133 | positive row contradiction | C04134 |
| N03501 | C04135 | uniform sharp terminal | C04136 |
| N03502 | none | positive row contradiction | C04137 |
| N03503 | none | positive row contradiction | C04138 |
| N03504 | none | positive row contradiction | C04139 |
| N03505 | none | positive row contradiction | C04140 |
| N03506 | C04141 | angle(8,6437/65536) | N03507, N03520 |
| N03507 | C04142 | sat(2,7) | N03508, N03511, N03512, N03513, N03514, N03517, N03518, N03519 |
| N03508 | C04143 | angle(4,-3693/131072) | N03509, N03510 |
| N03509 | C04144 | positive row contradiction | C04145 |
| N03510 | C04146 | uniform sharp terminal | C04147 |
| N03511 | none | positive row contradiction | C04148 |
| N03512 | none | positive row contradiction | C04149 |
| N03513 | none | positive row contradiction | C04150 |
| N03514 | C04151 | angle(4,-3383/131072) | N03515, N03516 |
| N03515 | C04152 | uniform sharp terminal from box | C04152 |
| N03516 | C04153 | uniform sharp terminal | C04154 |
| N03517 | none | positive row contradiction | C04155 |
| N03518 | none | positive row contradiction | C04156 |
| N03519 | none | positive row contradiction | C04157 |
| N03520 | none | positive row contradiction | C04158 |
| N03521 | none | positive row contradiction | C04159 |
| N03522 | C04160 | proxy(6,8) | N03523, N03524, N03525, N03526 |
| N03523 | none | positive row contradiction | C04161 |
| N03524 | none | positive row contradiction | C04162 |
| N03525 | C04163 | positive row contradiction | C04164 |
| N03526 | none | positive row contradiction | C04165 |
| N03527 | C04166 | positive row contradiction | C04167 |
| N03528 | C04168 | angle(8,13573/65536) | N03529, N03530 |
| N03529 | C04169 | positive row contradiction | C04170 |
| N03530 | none | positive row contradiction | C04171 |
| N03531 | none | positive row contradiction | C04172 |
| N03532 | C04173 | angle(4,-26295/131072) | N03533, N03534 |
| N03533 | none | positive row contradiction | C04174 |
| N03534 | C04175 | proxy(5,8) | N03535, N03536, N03541, N03558 |
| N03535 | none | positive row contradiction | C04176 |
| N03536 | C04177 | proxy(3,8) | N03537, N03538, N03539, N03540 |
| N03537 | none | positive row contradiction | C04178 |
| N03538 | none | positive row contradiction | C04179 |
| N03539 | C04180 | positive row contradiction | C04181 |
| N03540 | C04182 | positive row contradiction | C04183 |
| N03541 | C04184 | angle(8,13573/65536) | N03542, N03555 |
| N03542 | C04185 | proxy(6,8) | N03543, N03544, N03545, N03554 |
| N03543 | none | positive row contradiction | C04186 |
| N03544 | none | positive row contradiction | C04187 |
| N03545 | C04188 | proxy(2,8) | N03546, N03547, N03548, N03549 |
| N03546 | none | positive row contradiction | C04189 |
| N03547 | none | positive row contradiction | C04190 |
| N03548 | none | positive row contradiction | C04191 |
| N03549 | C04192 | angle(8,717/8192) | N03550, N03553 |
| N03550 | C04193 | angle(4,-723/16384) | N03551, N03552 |
| N03551 | C04194 | positive row contradiction | C04195 |
| N03552 | C04196 | uniform sharp terminal | C04197 |
| N03553 | none | positive row contradiction | C04198 |
| N03554 | none | positive row contradiction | C04199 |
| N03555 | C04200 | angle(8,40719/131072) | N03556, N03557 |
| N03556 | C04201 | positive row contradiction | C04202 |
| N03557 | C04203 | positive row contradiction | C04204 |
| N03558 | none | positive row contradiction | C04205 |
| N03559 | C04206 | angle(4,-26295/131072) | N03560, N03561 |
| N03560 | none | positive row contradiction | C04207 |
| N03561 | C04208 | angle(8,13573/65536) | N03562, N03563 |
| N03562 | C04209 | positive row contradiction | C04210 |
| N03563 | none | positive row contradiction | C04211 |
| N03564 | C04212 | angle(6,10669/65536) | N03565, N03566 |
| N03565 | none | positive row contradiction | C04213 |
| N03566 | none | positive row contradiction | C04214 |
| N03567 | C04215 | proxy(2,8) | N03568, N03579, N03580, N03581 |
| N03568 | C04216 | angle(8,13573/65536) | N03569, N03574 |
| N03569 | C04217 | proxy(7,8) | N03570, N03571, N03572, N03573 |
| N03570 | none | positive row contradiction | C04218 |
| N03571 | C04219 | positive row contradiction | C04220 |
| N03572 | none | positive row contradiction | C04221 |
| N03573 | none | positive row contradiction | C04222 |
| N03574 | C04223 | proxy(7,8) | N03575, N03576, N03577, N03578 |
| N03575 | none | positive row contradiction | C04224 |
| N03576 | C04225 | positive row contradiction | C04226 |
| N03577 | none | positive row contradiction | C04227 |
| N03578 | none | positive row contradiction | C04228 |
| N03579 | none | positive row contradiction | C04229 |
| N03580 | none | positive row contradiction | C04230 |
| N03581 | none | positive row contradiction | C04231 |
| N03582 | C04232 | proxy(5,8) | N03583, N03584, N03585, N03608 |
| N03583 | C04233 | positive row contradiction | C04234 |
| N03584 | C04235 | positive row contradiction | C04236 |
| N03585 | C04237 | proxy(3,8) | N03586, N03605, N03606, N03607 |
| N03586 | C04238 | sat(6,8) | N03587, N03592, N03593, N03594, N03595, N03602, N03603, N03604 |
| N03587 | C04239 | angle(7,13573/65536) | N03588, N03591 |
| N03588 | C04240 | angle(8,28667/131072) | N03589, N03590 |
| N03589 | C04241 | positive row contradiction | C04242 |
| N03590 | none | positive row contradiction | C04243 |
| N03591 | C04244 | positive row contradiction | C04245 |
| N03592 | none | positive row contradiction | C04246 |
| N03593 | none | positive row contradiction | C04247 |
| N03594 | none | positive row contradiction | C04248 |
| N03595 | C04249 | proxy(4,8) | N03596, N03597, N03600, N03601 |
| N03596 | none | positive row contradiction | C04250 |
| N03597 | C04251 | angle(7,13573/65536) | N03598, N03599 |
| N03598 | C04252 | positive row contradiction | C04253 |
| N03599 | none | positive row contradiction | C04254 |
| N03600 | none | positive row contradiction | C04255 |
| N03601 | none | positive row contradiction | C04256 |
| N03602 | none | positive row contradiction | C04257 |
| N03603 | none | positive row contradiction | C04258 |
| N03604 | C04259 | positive row contradiction | C04260 |
| N03605 | none | positive row contradiction | C04261 |
| N03606 | none | positive row contradiction | C04262 |
| N03607 | none | positive row contradiction | C04263 |
| N03608 | C04264 | angle(7,13573/65536) | N03609, N03610 |
| N03609 | C04265 | positive row contradiction | C04266 |
| N03610 | none | positive row contradiction | C04267 |
| N03611 | C04268 | angle(3,-13573/65536) | N03612, N03613 |
| N03612 | C04269 | positive row contradiction | C04270 |
| N03613 | C04271 | angle(8,0) | N03614, N04129 |
| N03614 | C04272 | proxy(7,8) | N03615, N03616, N04015, N04016 |
| N03615 | none | positive row contradiction | C04273 |
| N03616 | C04274 | angle(6,13573/65536) | N03617, N04014 |
| N03617 | C04275 | sat(2,7) | N03618, N03879, N03880, N03881, N03882, N04011, N04012, N04013 |
| N03618 | C04276 | angle(4,12769/65536) | N03619, N03878 |
| N03619 | C04277 | angle(8,-13573/65536) | N03620, N03733 |
| N03620 | C04278 | angle(7,13573/65536) | N03621, N03658 |
| N03621 | C04279 | sat(1,8) | N03622, N03623, N03632, N03633, N03638, N03639, N03644, N03645 |
| N03622 | none | positive row contradiction | C04280 |
| N03623 | C04281 | sat(3,8) | N03624, N03625, N03626, N03627, N03628, N03629, N03630, N03631 |
| N03624 | none | positive row contradiction | C04282 |
| N03625 | none | positive row contradiction | C04283 |
| N03626 | none | positive row contradiction | C04284 |
| N03627 | none | positive row contradiction | C04285 |
| N03628 | C04286 | positive row contradiction | C04287 |
| N03629 | none | positive row contradiction | C04288 |
| N03630 | C04289 | positive row contradiction | C04290 |
| N03631 | none | positive row contradiction | C04291 |
| N03632 | C04292 | positive row contradiction | C04293 |
| N03633 | C04294 | proxy(5,8) | N03634, N03635, N03636, N03637 |
| N03634 | none | positive row contradiction | C04295 |
| N03635 | none | positive row contradiction | C04296 |
| N03636 | none | positive row contradiction | C04297 |
| N03637 | none | positive row contradiction | C04298 |
| N03638 | none | positive row contradiction | C04299 |
| N03639 | C04300 | proxy(2,8) | N03640, N03641, N03642, N03643 |
| N03640 | none | positive row contradiction | C04301 |
| N03641 | none | positive row contradiction | C04302 |
| N03642 | none | positive row contradiction | C04303 |
| N03643 | C04304 | positive row contradiction | C04305 |
| N03644 | none | positive row contradiction | C04306 |
| N03645 | C04307 | proxy(3,8) | N03646, N03651, N03652, N03653 |
| N03646 | C04308 | proxy(5,8) | N03647, N03648, N03649, N03650 |
| N03647 | none | positive row contradiction | C04309 |
| N03648 | none | positive row contradiction | C04310 |
| N03649 | C04311 | positive row contradiction | C04312 |
| N03650 | none | positive row contradiction | C04313 |
| N03651 | none | positive row contradiction | C04314 |
| N03652 | none | positive row contradiction | C04315 |
| N03653 | C04316 | proxy(5,8) | N03654, N03655, N03656, N03657 |
| N03654 | none | positive row contradiction | C04317 |
| N03655 | none | positive row contradiction | C04318 |
| N03656 | none | positive row contradiction | C04319 |
| N03657 | none | positive row contradiction | C04320 |
| N03658 | C04321 | angle(8,-40719/131072) | N03659, N03684 |
| N03659 | C04322 | proxy(1,8) | N03660, N03661, N03678, N03679 |
| N03660 | none | positive row contradiction | C04323 |
| N03661 | C04324 | sat(1,8) | N03662, N03663, N03668, N03669, N03670, N03671, N03676, N03677 |
| N03662 | none | positive row contradiction | C04325 |
| N03663 | C04326 | proxy(6,8) | N03664, N03665, N03666, N03667 |
| N03664 | none | positive row contradiction | C04327 |
| N03665 | none | positive row contradiction | C04328 |
| N03666 | C04329 | positive row contradiction | C04330 |
| N03667 | none | positive row contradiction | C04331 |
| N03668 | none | positive row contradiction | C04332 |
| N03669 | C04333 | positive row contradiction | C04334 |
| N03670 | none | positive row contradiction | C04335 |
| N03671 | C04336 | proxy(3,8) | N03672, N03673, N03674, N03675 |
| N03672 | C04337 | positive row contradiction | C04338 |
| N03673 | none | positive row contradiction | C04339 |
| N03674 | none | positive row contradiction | C04340 |
| N03675 | none | positive row contradiction | C04341 |
| N03676 | none | positive row contradiction | C04342 |
| N03677 | C04343 | positive row contradiction | C04344 |
| N03678 | C04345 | positive row contradiction | C04346 |
| N03679 | C04347 | proxy(5,8) | N03680, N03681, N03682, N03683 |
| N03680 | none | positive row contradiction | C04348 |
| N03681 | none | positive row contradiction | C04349 |
| N03682 | none | positive row contradiction | C04350 |
| N03683 | none | positive row contradiction | C04351 |
| N03684 | C04352 | sat(7,8) | N03685, N03686, N03701, N03702, N03707, N03708, N03717, N03718 |
| N03685 | none | positive row contradiction | C04353 |
| N03686 | C04354 | proxy(6,8) | N03687, N03692, N03693, N03700 |
| N03687 | C04355 | proxy(5,8) | N03688, N03689, N03690, N03691 |
| N03688 | none | positive row contradiction | C04356 |
| N03689 | none | positive row contradiction | C04357 |
| N03690 | C04358 | positive row contradiction | C04359 |
| N03691 | none | positive row contradiction | C04360 |
| N03692 | none | positive row contradiction | C04361 |
| N03693 | C04362 | proxy(1,8) | N03694, N03695, N03698, N03699 |
| N03694 | none | positive row contradiction | C04363 |
| N03695 | C04364 | angle(8,-67865/262144) | N03696, N03697 |
| N03696 | C04365 | positive row contradiction | C04366 |
| N03697 | C04367 | positive row contradiction | C04368 |
| N03698 | C04369 | positive row contradiction | C04370 |
| N03699 | none | positive row contradiction | C04371 |
| N03700 | none | positive row contradiction | C04372 |
| N03701 | C04373 | positive row contradiction | C04374 |
| N03702 | C04375 | proxy(5,8) | N03703, N03704, N03705, N03706 |
| N03703 | none | positive row contradiction | C04376 |
| N03704 | none | positive row contradiction | C04377 |
| N03705 | C04378 | positive row contradiction | C04379 |
| N03706 | none | positive row contradiction | C04380 |
| N03707 | none | positive row contradiction | C04381 |
| N03708 | C04382 | proxy(2,8) | N03709, N03710, N03711, N03712 |
| N03709 | none | positive row contradiction | C04383 |
| N03710 | none | positive row contradiction | C04384 |
| N03711 | none | positive row contradiction | C04385 |
| N03712 | C04386 | proxy(6,8) | N03713, N03714, N03715, N03716 |
| N03713 | none | positive row contradiction | C04387 |
| N03714 | none | positive row contradiction | C04388 |
| N03715 | C04389 | positive row contradiction | C04390 |
| N03716 | none | positive row contradiction | C04391 |
| N03717 | none | positive row contradiction | C04392 |
| N03718 | C04393 | proxy(1,8) | N03719, N03720, N03727, N03728 |
| N03719 | none | positive row contradiction | C04394 |
| N03720 | C04395 | proxy(2,8) | N03721, N03722, N03723, N03724 |
| N03721 | none | positive row contradiction | C04396 |
| N03722 | none | positive row contradiction | C04397 |
| N03723 | none | positive row contradiction | C04398 |
| N03724 | C04399 | angle(8,-67865/262144) | N03725, N03726 |
| N03725 | C04400 | positive row contradiction | C04401 |
| N03726 | C04402 | positive row contradiction | C04403 |
| N03727 | C04404 | positive row contradiction | C04405 |
| N03728 | C04406 | proxy(5,8) | N03729, N03730, N03731, N03732 |
| N03729 | none | positive row contradiction | C04407 |
| N03730 | none | positive row contradiction | C04408 |
| N03731 | none | positive row contradiction | C04409 |
| N03732 | none | positive row contradiction | C04410 |
| N03733 | C04411 | angle(7,13573/65536) | N03734, N03811 |
| N03734 | C04412 | sat(1,8) | N03735, N03736, N03761, N03762, N03767, N03768, N03797, N03798 |
| N03735 | none | positive row contradiction | C04413 |
| N03736 | C04414 | angle(8,-13573/131072) | N03737, N03746 |
| N03737 | C04415 | proxy(6,8) | N03738, N03739, N03740, N03745 |
| N03738 | none | positive row contradiction | C04416 |
| N03739 | none | positive row contradiction | C04417 |
| N03740 | C04418 | proxy(5,8) | N03741, N03742, N03743, N03744 |
| N03741 | none | positive row contradiction | C04419 |
| N03742 | none | positive row contradiction | C04420 |
| N03743 | C04421 | positive row contradiction | C04422 |
| N03744 | none | positive row contradiction | C04423 |
| N03745 | none | positive row contradiction | C04424 |
| N03746 | C04425 | proxy(2,8) | N03747, N03748, N03749, N03750 |
| N03747 | none | positive row contradiction | C04426 |
| N03748 | none | positive row contradiction | C04427 |
| N03749 | none | positive row contradiction | C04428 |
| N03750 | C04429 | proxy(1,4) | N03751, N03752, N03753, N03754 |
| N03751 | none | positive row contradiction | C04430 |
| N03752 | none | positive row contradiction | C04431 |
| N03753 | none | positive row contradiction | C04432 |
| N03754 | C04433 | angle(8,-13573/262144) | N03755, N03756 |
| N03755 | C04434 | positive row contradiction | C04435 |
| N03756 | C04436 | proxy(6,8) | N03757, N03758, N03759, N03760 |
| N03757 | none | positive row contradiction | C04437 |
| N03758 | none | positive row contradiction | C04438 |
| N03759 | C04439 | uniform sharp terminal | C04440 |
| N03760 | none | positive row contradiction | C04441 |
| N03761 | C04442 | positive row contradiction | C04443 |
| N03762 | C04444 | proxy(5,8) | N03763, N03764, N03765, N03766 |
| N03763 | none | positive row contradiction | C04445 |
| N03764 | none | positive row contradiction | C04446 |
| N03765 | none | positive row contradiction | C04447 |
| N03766 | none | positive row contradiction | C04448 |
| N03767 | none | positive row contradiction | C04449 |
| N03768 | C04450 | proxy(2,8) | N03769, N03770, N03771, N03772 |
| N03769 | none | positive row contradiction | C04451 |
| N03770 | none | positive row contradiction | C04452 |
| N03771 | none | positive row contradiction | C04453 |
| N03772 | C04454 | angle(8,-13573/131072) | N03773, N03778 |
| N03773 | C04455 | proxy(5,8) | N03774, N03775, N03776, N03777 |
| N03774 | none | positive row contradiction | C04456 |
| N03775 | none | positive row contradiction | C04457 |
| N03776 | C04458 | positive row contradiction | C04459 |
| N03777 | none | positive row contradiction | C04460 |
| N03778 | C04461 | angle(8,-13573/262144) | N03779, N03788 |
| N03779 | C04462 | sat(1,7) | N03780, N03781, N03782, N03783, N03784, N03785, N03786, N03787 |
| N03780 | none | positive row contradiction | C04463 |
| N03781 | none | positive row contradiction | C04464 |
| N03782 | C04465 | positive row contradiction | C04466 |
| N03783 | none | positive row contradiction | C04467 |
| N03784 | none | positive row contradiction | C04468 |
| N03785 | none | positive row contradiction | C04469 |
| N03786 | C04470 | positive row contradiction | C04471 |
| N03787 | none | positive row contradiction | C04472 |
| N03788 | C04473 | angle(8,-13573/524288) | N03789, N03794 |
| N03789 | C04474 | proxy(6,8) | N03790, N03791, N03792, N03793 |
| N03790 | none | positive row contradiction | C04475 |
| N03791 | none | positive row contradiction | C04476 |
| N03792 | C04477 | positive row contradiction | C04478 |
| N03793 | none | positive row contradiction | C04479 |
| N03794 | C04480 | angle(6,1071/65536) | N03795, N03796 |
| N03795 | C04481 | uniform sharp terminal | C04482 |
| N03796 | C04483 | positive row contradiction | C04484 |
| N03797 | C04485 | positive row contradiction | C04486 |
| N03798 | C04487 | proxy(3,8) | N03799, N03804, N03805, N03806 |
| N03799 | C04488 | proxy(5,8) | N03800, N03801, N03802, N03803 |
| N03800 | none | positive row contradiction | C04489 |
| N03801 | none | positive row contradiction | C04490 |
| N03802 | C04491 | positive row contradiction | C04492 |
| N03803 | none | positive row contradiction | C04493 |
| N03804 | none | positive row contradiction | C04494 |
| N03805 | none | positive row contradiction | C04495 |
| N03806 | C04496 | proxy(5,8) | N03807, N03808, N03809, N03810 |
| N03807 | none | positive row contradiction | C04497 |
| N03808 | none | positive row contradiction | C04498 |
| N03809 | none | positive row contradiction | C04499 |
| N03810 | none | positive row contradiction | C04500 |
| N03811 | C04501 | proxy(5,8) | N03812, N03813, N03818, N03877 |
| N03812 | none | positive row contradiction | C04502 |
| N03813 | C04503 | proxy(2,8) | N03814, N03815, N03816, N03817 |
| N03814 | none | positive row contradiction | C04504 |
| N03815 | none | positive row contradiction | C04505 |
| N03816 | none | positive row contradiction | C04506 |
| N03817 | C04507 | positive row contradiction | C04508 |
| N03818 | C04509 | proxy(1,8) | N03819, N03820, N03875, N03876 |
| N03819 | none | positive row contradiction | C04510 |
| N03820 | C04511 | angle(8,-13573/131072) | N03821, N03858 |
| N03821 | C04512 | sat(5,8) | N03822, N03823, N03824, N03837, N03838, N03839, N03848, N03857 |
| N03822 | none | positive row contradiction | C04513 |
| N03823 | C04514 | positive row contradiction | C04515 |
| N03824 | C04516 | proxy(3,8) | N03825, N03834, N03835, N03836 |
| N03825 | C04517 | sat(2,8) | N03826, N03827, N03828, N03829, N03830, N03831, N03832, N03833 |
| N03826 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N03827 | none | positive row contradiction | C04518 |
| N03828 | none | positive row contradiction | C04519 |
| N03829 | C04520 | positive row contradiction | C04521 |
| N03830 | none | positive row contradiction | C04522 |
| N03831 | none | positive row contradiction | C04523 |
| N03832 | none | positive row contradiction | C04524 |
| N03833 | C04525 | positive row contradiction | C04526 |
| N03834 | none | positive row contradiction | C04527 |
| N03835 | none | positive row contradiction | C04528 |
| N03836 | none | positive row contradiction | C04529 |
| N03837 | none | positive row contradiction | C04530 |
| N03838 | none | positive row contradiction | C04531 |
| N03839 | C04532 | sat(2,8) | N03840, N03841, N03842, N03843, N03844, N03845, N03846, N03847 |
| N03840 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N03841 | none | positive row contradiction | C04533 |
| N03842 | none | positive row contradiction | C04534 |
| N03843 | none | positive row contradiction | C04535 |
| N03844 | none | positive row contradiction | C04536 |
| N03845 | none | positive row contradiction | C04537 |
| N03846 | none | positive row contradiction | C04538 |
| N03847 | none | positive row contradiction | C04539 |
| N03848 | C04540 | sat(2,8) | N03849, N03850, N03851, N03852, N03853, N03854, N03855, N03856 |
| N03849 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N03850 | none | positive row contradiction | C04541 |
| N03851 | none | positive row contradiction | C04542 |
| N03852 | C04543 | positive row contradiction | C04544 |
| N03853 | none | positive row contradiction | C04545 |
| N03854 | none | positive row contradiction | C04546 |
| N03855 | none | positive row contradiction | C04547 |
| N03856 | C04548 | positive row contradiction | C04549 |
| N03857 | none | positive row contradiction | C04550 |
| N03858 | C04551 | proxy(6,8) | N03859, N03860, N03861, N03874 |
| N03859 | none | positive row contradiction | C04552 |
| N03860 | none | positive row contradiction | C04553 |
| N03861 | C04554 | sat(1,7) | N03862, N03863, N03864, N03869, N03870, N03871, N03872, N03873 |
| N03862 | none | positive row contradiction | C04555 |
| N03863 | none | positive row contradiction | C04556 |
| N03864 | C04557 | angle(8,-13573/262144) | N03865, N03866 |
| N03865 | C04558 | positive row contradiction | C04559 |
| N03866 | C04560 | angle(8,-13573/524288) | N03867, N03868 |
| N03867 | C04561 | positive row contradiction | C04562 |
| N03868 | C04563 | uniform sharp terminal | C04564 |
| N03869 | none | positive row contradiction | C04565 |
| N03870 | none | positive row contradiction | C04566 |
| N03871 | none | positive row contradiction | C04567 |
| N03872 | none | positive row contradiction | C04568 |
| N03873 | none | positive row contradiction | C04569 |
| N03874 | none | positive row contradiction | C04570 |
| N03875 | C04571 | positive row contradiction | C04572 |
| N03876 | none | positive row contradiction | C04573 |
| N03877 | none | positive row contradiction | C04574 |
| N03878 | none | positive row contradiction | C04575 |
| N03879 | none | positive row contradiction | C04576 |
| N03880 | none | positive row contradiction | C04577 |
| N03881 | none | positive row contradiction | C04578 |
| N03882 | C04579 | angle(8,-13573/65536) | N03883, N03916 |
| N03883 | C04580 | sat(1,8) | N03884, N03885, N03890, N03891, N03896, N03897, N03902, N03903 |
| N03884 | none | positive row contradiction | C04581 |
| N03885 | C04582 | proxy(6,8) | N03886, N03887, N03888, N03889 |
| N03886 | none | positive row contradiction | C04583 |
| N03887 | none | positive row contradiction | C04584 |
| N03888 | C04585 | positive row contradiction | C04586 |
| N03889 | none | positive row contradiction | C04587 |
| N03890 | C04588 | positive row contradiction | C04589 |
| N03891 | C04590 | proxy(5,8) | N03892, N03893, N03894, N03895 |
| N03892 | none | positive row contradiction | C04591 |
| N03893 | none | positive row contradiction | C04592 |
| N03894 | none | positive row contradiction | C04593 |
| N03895 | none | positive row contradiction | C04594 |
| N03896 | none | positive row contradiction | C04595 |
| N03897 | C04596 | proxy(2,8) | N03898, N03899, N03900, N03901 |
| N03898 | none | positive row contradiction | C04597 |
| N03899 | none | positive row contradiction | C04598 |
| N03900 | none | positive row contradiction | C04599 |
| N03901 | C04600 | positive row contradiction | C04601 |
| N03902 | C04602 | positive row contradiction | C04603 |
| N03903 | C04604 | proxy(5,8) | N03904, N03905, N03910, N03915 |
| N03904 | none | positive row contradiction | C04605 |
| N03905 | C04606 | proxy(3,8) | N03906, N03907, N03908, N03909 |
| N03906 | none | positive row contradiction | C04607 |
| N03907 | none | positive row contradiction | C04608 |
| N03908 | none | positive row contradiction | C04609 |
| N03909 | none | positive row contradiction | C04610 |
| N03910 | C04611 | proxy(3,8) | N03911, N03912, N03913, N03914 |
| N03911 | C04612 | positive row contradiction | C04613 |
| N03912 | none | positive row contradiction | C04614 |
| N03913 | none | positive row contradiction | C04615 |
| N03914 | none | positive row contradiction | C04616 |
| N03915 | none | positive row contradiction | C04617 |
| N03916 | C04618 | sat(1,8) | N03917, N03918, N03953, N03958, N03963, N03964, N03999, N04004 |
| N03917 | none | positive row contradiction | C04619 |
| N03918 | C04620 | proxy(6,8) | N03919, N03920, N03921, N03952 |
| N03919 | none | positive row contradiction | C04621 |
| N03920 | none | positive row contradiction | C04622 |
| N03921 | C04623 | sat(1,7) | N03922, N03923, N03924, N03933, N03934, N03935, N03936, N03951 |
| N03922 | none | positive row contradiction | C04624 |
| N03923 | none | positive row contradiction | C04625 |
| N03924 | C04626 | proxy(5,8) | N03925, N03926, N03927, N03932 |
| N03925 | none | positive row contradiction | C04627 |
| N03926 | none | positive row contradiction | C04628 |
| N03927 | C04629 | angle(8,-1173/16384) | N03928, N03929 |
| N03928 | none | positive row contradiction | C04630 |
| N03929 | C04631 | angle(8,-4233/131072) | N03930, N03931 |
| N03930 | C04632 | uniform sharp terminal from box | C04632 |
| N03931 | C04633 | uniform sharp terminal | C04634 |
| N03932 | none | positive row contradiction | C04635 |
| N03933 | none | positive row contradiction | C04636 |
| N03934 | none | positive row contradiction | C04637 |
| N03935 | none | common-axis chain [[7,0],[1,7,2]] | endpoint squared distance < 4 |
| N03936 | C04638 | angle(8,-13573/131072) | N03937, N03938 |
| N03937 | C04639 | positive row contradiction | C04640 |
| N03938 | C04641 | sat(1,4) | N03939, N03940, N03941, N03942, N03945, N03946, N03947, N03948 |
| N03939 | none | positive row contradiction | C04642 |
| N03940 | none | positive row contradiction | C04643 |
| N03941 | none | positive row contradiction | C04644 |
| N03942 | C04645 | angle(8,-2159/65536) | N03943, N03944 |
| N03943 | C04646 | uniform sharp terminal from box | C04646 |
| N03944 | C04647 | uniform sharp terminal | C04648 |
| N03945 | none | positive row contradiction | C04649 |
| N03946 | none | positive row contradiction | C04650 |
| N03947 | none | positive row contradiction | C04651 |
| N03948 | C04652 | angle(8,-2159/65536) | N03949, N03950 |
| N03949 | C04653 | uniform sharp terminal from box | C04653 |
| N03950 | C04654 | uniform sharp terminal | C04655 |
| N03951 | none | positive row contradiction | C04656 |
| N03952 | none | positive row contradiction | C04657 |
| N03953 | C04658 | proxy(2,8) | N03954, N03955, N03956, N03957 |
| N03954 | none | positive row contradiction | C04659 |
| N03955 | none | positive row contradiction | C04660 |
| N03956 | none | positive row contradiction | C04661 |
| N03957 | none | positive row contradiction | C04662 |
| N03958 | C04663 | proxy(5,8) | N03959, N03960, N03961, N03962 |
| N03959 | none | positive row contradiction | C04664 |
| N03960 | none | positive row contradiction | C04665 |
| N03961 | none | positive row contradiction | C04666 |
| N03962 | none | positive row contradiction | C04667 |
| N03963 | none | positive row contradiction | C04668 |
| N03964 | C04669 | proxy(2,8) | N03965, N03966, N03967, N03968 |
| N03965 | none | positive row contradiction | C04670 |
| N03966 | none | positive row contradiction | C04671 |
| N03967 | none | positive row contradiction | C04672 |
| N03968 | C04673 | proxy(3,8) | N03969, N03996, N03997, N03998 |
| N03969 | C04674 | sat(2,8) | N03970, N03971, N03972, N03973, N03986, N03987, N03988, N03989 |
| N03970 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N03971 | none | positive row contradiction | C04675 |
| N03972 | none | positive row contradiction | C04676 |
| N03973 | C04677 | sat(0,4) | N03974, N03975, N03976, N03977, N03980, N03981, N03982, N03983 |
| N03974 | none | positive row contradiction | C04678 |
| N03975 | none | positive row contradiction | C04679 |
| N03976 | none | positive row contradiction | C04680 |
| N03977 | C04681 | angle(8,-817/16384) | N03978, N03979 |
| N03978 | none | positive row contradiction | C04682 |
| N03979 | C04683 | uniform sharp terminal | C04684 |
| N03980 | none | positive row contradiction | C04685 |
| N03981 | none | positive row contradiction | C04686 |
| N03982 | none | positive row contradiction | C04687 |
| N03983 | C04688 | angle(8,-817/16384) | N03984, N03985 |
| N03984 | none | positive row contradiction | C04689 |
| N03985 | C04690 | uniform sharp terminal | C04691 |
| N03986 | none | common-axis chain [[8,0],[1,8,2]] | endpoint squared distance < 4 |
| N03987 | none | positive row contradiction | C04692 |
| N03988 | none | positive row contradiction | C04693 |
| N03989 | C04694 | proxy(6,8) | N03990, N03991, N03992, N03995 |
| N03990 | none | positive row contradiction | C04695 |
| N03991 | none | positive row contradiction | C04696 |
| N03992 | C04697 | angle(8,-1463/32768) | N03993, N03994 |
| N03993 | none | positive row contradiction | C04698 |
| N03994 | C04699 | uniform sharp terminal | C04700 |
| N03995 | none | positive row contradiction | C04701 |
| N03996 | none | positive row contradiction | C04702 |
| N03997 | none | positive row contradiction | C04703 |
| N03998 | C04704 | positive row contradiction | C04705 |
| N03999 | C04706 | proxy(2,8) | N04000, N04001, N04002, N04003 |
| N04000 | none | positive row contradiction | C04707 |
| N04001 | none | positive row contradiction | C04708 |
| N04002 | none | positive row contradiction | C04709 |
| N04003 | none | positive row contradiction | C04710 |
| N04004 | C04711 | proxy(5,8) | N04005, N04006, N04007, N04010 |
| N04005 | none | positive row contradiction | C04712 |
| N04006 | C04713 | positive row contradiction | C04714 |
| N04007 | C04715 | angle(7,13573/65536) | N04008, N04009 |
| N04008 | C04716 | positive row contradiction | C04717 |
| N04009 | none | positive row contradiction | C04718 |
| N04010 | none | positive row contradiction | C04719 |
| N04011 | none | positive row contradiction | C04720 |
| N04012 | none | positive row contradiction | C04721 |
| N04013 | C04722 | positive row contradiction | C04723 |
| N04014 | C04724 | positive row contradiction | C04725 |
| N04015 | C04726 | positive row contradiction | C04727 |
| N04016 | C04728 | angle(6,13573/65536) | N04017, N04128 |
| N04017 | C04729 | proxy(1,8) | N04018, N04019, N04108, N04109 |
| N04018 | none | positive row contradiction | C04730 |
| N04019 | C04731 | proxy(5,8) | N04020, N04021, N04026, N04107 |
| N04020 | none | positive row contradiction | C04732 |
| N04021 | C04733 | proxy(6,8) | N04022, N04023, N04024, N04025 |
| N04022 | none | positive row contradiction | C04734 |
| N04023 | none | positive row contradiction | C04735 |
| N04024 | C04736 | positive row contradiction | C04737 |
| N04025 | none | positive row contradiction | C04738 |
| N04026 | C04739 | sat(1,8) | N04027, N04028, N04071, N04072, N04073, N04074, N04103, N04104 |
| N04027 | none | positive row contradiction | C04740 |
| N04028 | C04741 | sat(2,8) | N04029, N04030, N04031, N04032, N04051, N04052, N04053, N04054 |
| N04029 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N04030 | none | positive row contradiction | C04742 |
| N04031 | none | positive row contradiction | C04743 |
| N04032 | C04744 | proxy(0,7) | N04033, N04034, N04037, N04050 |
| N04033 | none | positive row contradiction | C04745 |
| N04034 | C04746 | angle(4,3201/65536) | N04035, N04036 |
| N04035 | C04747 | uniform sharp terminal | C04748 |
| N04036 | C04749 | positive row contradiction | C04750 |
| N04037 | C04751 | sat(2,7) | N04038, N04041, N04042, N04043, N04044, N04047, N04048, N04049 |
| N04038 | C04752 | angle(4,2433/65536) | N04039, N04040 |
| N04039 | C04753 | uniform sharp terminal | C04754 |
| N04040 | C04755 | positive row contradiction | C04756 |
| N04041 | none | positive row contradiction | C04757 |
| N04042 | none | positive row contradiction | C04758 |
| N04043 | none | positive row contradiction | C04759 |
| N04044 | C04760 | angle(4,2433/65536) | N04045, N04046 |
| N04045 | C04761 | uniform sharp terminal | C04762 |
| N04046 | C04763 | positive row contradiction | C04764 |
| N04047 | none | positive row contradiction | C04765 |
| N04048 | none | positive row contradiction | C04766 |
| N04049 | C04767 | positive row contradiction | C04768 |
| N04050 | none | positive row contradiction | C04769 |
| N04051 | none | positive row contradiction | C04770 |
| N04052 | none | positive row contradiction | C04771 |
| N04053 | none | positive row contradiction | C04772 |
| N04054 | C04773 | sat(1,7) | N04055, N04056, N04057, N04062, N04063, N04064, N04065, N04070 |
| N04055 | none | positive row contradiction | C04774 |
| N04056 | none | positive row contradiction | C04775 |
| N04057 | C04776 | angle(8,-6925/131072) | N04058, N04059 |
| N04058 | none | positive row contradiction | C04777 |
| N04059 | C04778 | angle(4,2433/65536) | N04060, N04061 |
| N04060 | C04779 | uniform sharp terminal | C04780 |
| N04061 | C04781 | positive row contradiction | C04782 |
| N04062 | none | positive row contradiction | C04783 |
| N04063 | C04784 | positive row contradiction | C04785 |
| N04064 | none | positive row contradiction | C04786 |
| N04065 | C04787 | angle(8,-6925/131072) | N04066, N04067 |
| N04066 | none | positive row contradiction | C04788 |
| N04067 | C04789 | angle(4,2433/65536) | N04068, N04069 |
| N04068 | C04790 | uniform sharp terminal | C04791 |
| N04069 | C04792 | positive row contradiction | C04793 |
| N04070 | none | positive row contradiction | C04794 |
| N04071 | none | positive row contradiction | C04795 |
| N04072 | none | positive row contradiction | C04796 |
| N04073 | none | positive row contradiction | C04797 |
| N04074 | C04798 | sat(2,8) | N04075, N04076, N04077, N04078, N04085, N04086, N04087, N04088 |
| N04075 | none | common-axis chain [[2,0],[8,2,3]] | endpoint squared distance < 4 |
| N04076 | none | positive row contradiction | C04799 |
| N04077 | none | positive row contradiction | C04800 |
| N04078 | C04801 | angle(8,-17495/131072) | N04079, N04080 |
| N04079 | none | positive row contradiction | C04802 |
| N04080 | C04803 | angle(4,3201/65536) | N04081, N04084 |
| N04081 | C04804 | angle(8,-2047/65536) | N04082, N04083 |
| N04082 | C04805 | positive row contradiction | C04806 |
| N04083 | C04807 | uniform sharp terminal | C04808 |
| N04084 | C04809 | positive row contradiction | C04810 |
| N04085 | none | common-axis chain [[8,0],[1,8,2]] | endpoint squared distance < 4 |
| N04086 | none | positive row contradiction | C04811 |
| N04087 | none | positive row contradiction | C04812 |
| N04088 | C04813 | angle(8,-8827/65536) | N04089, N04090 |
| N04089 | none | positive row contradiction | C04814 |
| N04090 | C04815 | sat(2,7) | N04091, N04094, N04095, N04096, N04097, N04100, N04101, N04102 |
| N04091 | C04816 | angle(4,2433/65536) | N04092, N04093 |
| N04092 | C04817 | uniform sharp terminal | C04818 |
| N04093 | C04819 | positive row contradiction | C04820 |
| N04094 | none | positive row contradiction | C04821 |
| N04095 | none | positive row contradiction | C04822 |
| N04096 | none | positive row contradiction | C04823 |
| N04097 | C04824 | angle(4,2433/65536) | N04098, N04099 |
| N04098 | C04825 | uniform sharp terminal | C04826 |
| N04099 | C04827 | positive row contradiction | C04828 |
| N04100 | none | positive row contradiction | C04829 |
| N04101 | none | positive row contradiction | C04830 |
| N04102 | C04831 | positive row contradiction | C04832 |
| N04103 | none | positive row contradiction | C04833 |
| N04104 | C04834 | angle(8,-27279/131072) | N04105, N04106 |
| N04105 | none | positive row contradiction | C04835 |
| N04106 | none | positive row contradiction | C04836 |
| N04107 | C04837 | positive row contradiction | C04838 |
| N04108 | none | positive row contradiction | C04839 |
| N04109 | C04840 | proxy(3,8) | N04110, N04121, N04122, N04123 |
| N04110 | C04841 | proxy(6,8) | N04111, N04118, N04119, N04120 |
| N04111 | C04842 | proxy(5,8) | N04112, N04113, N04114, N04117 |
| N04112 | none | positive row contradiction | C04843 |
| N04113 | none | positive row contradiction | C04844 |
| N04114 | C04845 | angle(7,13573/65536) | N04115, N04116 |
| N04115 | C04846 | positive row contradiction | C04847 |
| N04116 | none | positive row contradiction | C04848 |
| N04117 | C04849 | positive row contradiction | C04850 |
| N04118 | none | positive row contradiction | C04851 |
| N04119 | none | positive row contradiction | C04852 |
| N04120 | none | positive row contradiction | C04853 |
| N04121 | none | positive row contradiction | C04854 |
| N04122 | none | positive row contradiction | C04855 |
| N04123 | C04856 | proxy(5,8) | N04124, N04125, N04126, N04127 |
| N04124 | C04857 | positive row contradiction | C04858 |
| N04125 | C04859 | positive row contradiction | C04860 |
| N04126 | none | positive row contradiction | C04861 |
| N04127 | C04862 | positive row contradiction | C04863 |
| N04128 | C04864 | positive row contradiction | C04865 |
| N04129 | C04866 | angle(4,13573/65536) | N04130, N04225 |
| N04130 | C04867 | angle(6,13573/65536) | N04131, N04224 |
| N04131 | C04868 | proxy(5,8) | N04132, N04137, N04142, N04221 |
| N04132 | C04869 | proxy(1,8) | N04133, N04134, N04135, N04136 |
| N04133 | none | positive row contradiction | C04870 |
| N04134 | none | positive row contradiction | C04871 |
| N04135 | C04872 | positive row contradiction | C04873 |
| N04136 | C04874 | positive row contradiction | C04875 |
| N04137 | C04876 | proxy(3,8) | N04138, N04139, N04140, N04141 |
| N04138 | none | positive row contradiction | C04877 |
| N04139 | none | positive row contradiction | C04878 |
| N04140 | C04879 | positive row contradiction | C04880 |
| N04141 | C04881 | positive row contradiction | C04882 |
| N04142 | C04883 | proxy(1,8) | N04143, N04144, N04195, N04202 |
| N04143 | none | positive row contradiction | C04884 |
| N04144 | C04885 | proxy(2,8) | N04145, N04146, N04147, N04148 |
| N04145 | none | positive row contradiction | C04886 |
| N04146 | none | positive row contradiction | C04887 |
| N04147 | none | positive row contradiction | C04888 |
| N04148 | C04889 | angle(7,13573/65536) | N04149, N04188 |
| N04149 | C04890 | sat(7,8) | N04150, N04151, N04164, N04165, N04172, N04173, N04180, N04181 |
| N04150 | none | positive row contradiction | C04891 |
| N04151 | C04892 | sat(6,8) | N04152, N04153, N04154, N04157, N04158, N04159, N04160, N04163 |
| N04152 | none | positive row contradiction | C04893 |
| N04153 | none | positive row contradiction | C04894 |
| N04154 | C04895 | angle(8,2497/65536) | N04155, N04156 |
| N04155 | C04896 | uniform sharp terminal | C04897 |
| N04156 | none | positive row contradiction | C04898 |
| N04157 | none | positive row contradiction | C04899 |
| N04158 | none | positive row contradiction | C04900 |
| N04159 | none | positive row contradiction | C04901 |
| N04160 | C04902 | angle(4,3767/131072) | N04161, N04162 |
| N04161 | C04903 | uniform sharp terminal | C04904 |
| N04162 | C04905 | positive row contradiction | C04906 |
| N04163 | none | positive row contradiction | C04907 |
| N04164 | none | positive row contradiction | C04908 |
| N04165 | C04909 | angle(8,13573/65536) | N04166, N04171 |
| N04166 | C04910 | angle(8,6225/65536) | N04167, N04170 |
| N04167 | C04911 | angle(8,5063/131072) | N04168, N04169 |
| N04168 | C04912 | uniform sharp terminal | C04913 |
| N04169 | none | positive row contradiction | C04914 |
| N04170 | none | positive row contradiction | C04915 |
| N04171 | none | positive row contradiction | C04916 |
| N04172 | none | positive row contradiction | C04917 |
| N04173 | C04918 | angle(8,13573/65536) | N04174, N04179 |
| N04174 | C04919 | angle(8,12459/131072) | N04175, N04178 |
| N04175 | C04920 | angle(8,5079/131072) | N04176, N04177 |
| N04176 | C04921 | uniform sharp terminal | C04922 |
| N04177 | none | positive row contradiction | C04923 |
| N04178 | none | positive row contradiction | C04924 |
| N04179 | none | positive row contradiction | C04925 |
| N04180 | none | positive row contradiction | C04926 |
| N04181 | C04927 | angle(8,2083/16384) | N04182, N04187 |
| N04182 | C04928 | angle(8,2083/32768) | N04183, N04186 |
| N04183 | C04929 | angle(8,2083/65536) | N04184, N04185 |
| N04184 | C04930 | uniform sharp terminal | C04931 |
| N04185 | C04932 | positive row contradiction | C04933 |
| N04186 | C04934 | positive row contradiction | C04935 |
| N04187 | C04936 | positive row contradiction | C04937 |
| N04188 | C04938 | angle(8,13573/65536) | N04189, N04194 |
| N04189 | C04939 | angle(8,13573/131072) | N04190, N04193 |
| N04190 | C04940 | angle(8,13573/262144) | N04191, N04192 |
| N04191 | C04941 | uniform sharp terminal | C04942 |
| N04192 | C04943 | positive row contradiction | C04944 |
| N04193 | C04945 | positive row contradiction | C04946 |
| N04194 | C04947 | positive row contradiction | C04948 |
| N04195 | C04949 | proxy(7,8) | N04196, N04197, N04200, N04201 |
| N04196 | none | positive row contradiction | C04950 |
| N04197 | C04951 | angle(7,13573/65536) | N04198, N04199 |
| N04198 | C04952 | positive row contradiction | C04953 |
| N04199 | C04954 | positive row contradiction | C04955 |
| N04200 | none | positive row contradiction | C04956 |
| N04201 | none | positive row contradiction | C04957 |
| N04202 | C04958 | sat(5,8) | N04203, N04204, N04205, N04206, N04207, N04208, N04209, N04220 |
| N04203 | none | positive row contradiction | C04959 |
| N04204 | C04960 | positive row contradiction | C04961 |
| N04205 | C04962 | positive row contradiction | C04963 |
| N04206 | none | positive row contradiction | C04964 |
| N04207 | C04965 | positive row contradiction | C04966 |
| N04208 | C04967 | positive row contradiction | C04968 |
| N04209 | C04969 | angle(7,13573/65536) | N04210, N04219 |
| N04210 | C04970 | sat(6,8) | N04211, N04212, N04213, N04214, N04215, N04216, N04217, N04218 |
| N04211 | C04971 | positive row contradiction | C04972 |
| N04212 | none | positive row contradiction | C04973 |
| N04213 | none | positive row contradiction | C04974 |
| N04214 | none | positive row contradiction | C04975 |
| N04215 | C04976 | positive row contradiction | C04977 |
| N04216 | none | positive row contradiction | C04978 |
| N04217 | none | positive row contradiction | C04979 |
| N04218 | none | common-axis chain [[8,1],[6,8,5]] | endpoint squared distance < 4 |
| N04219 | C04980 | positive row contradiction | C04981 |
| N04220 | none | positive row contradiction | C04982 |
| N04221 | C04983 | angle(8,13573/65536) | N04222, N04223 |
| N04222 | C04984 | positive row contradiction | C04985 |
| N04223 | none | positive row contradiction | C04986 |
| N04224 | C04987 | positive row contradiction | C04988 |
| N04225 | C04989 | proxy(1,8) | N04226, N04227, N04228, N04229 |
| N04226 | none | positive row contradiction | C04990 |
| N04227 | C04991 | positive row contradiction | C04992 |
| N04228 | C04993 | positive row contradiction | C04994 |
| N04229 | C04995 | positive row contradiction | C04996 |
| N04230 | none | F-above-B theorem | inconsistent F-below-B branch |
