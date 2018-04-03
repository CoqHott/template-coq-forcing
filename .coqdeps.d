forcing/TFUtils.vo forcing/TFUtils.glob forcing/TFUtils.v.beautified: forcing/TFUtils.v
forcing/TFUtils.vio: forcing/TFUtils.v
forcing/translation_utils.vo forcing/translation_utils.glob forcing/translation_utils.v.beautified: forcing/translation_utils.v
forcing/translation_utils.vio: forcing/translation_utils.v
forcing/TemplateForcing.vo forcing/TemplateForcing.glob forcing/TemplateForcing.v.beautified: forcing/TemplateForcing.v forcing/TFUtils.vo
forcing/TemplateForcing.vio: forcing/TemplateForcing.v forcing/TFUtils.vio
forcing/Tests.vo forcing/Tests.glob forcing/Tests.v.beautified: forcing/Tests.v forcing/TemplateForcing.vo
forcing/Tests.vio: forcing/Tests.v forcing/TemplateForcing.vio
forcing/GRTT.vo forcing/GRTT.glob forcing/GRTT.v.beautified: forcing/GRTT.v forcing/TemplateForcing.vo
forcing/GRTT.vio: forcing/GRTT.v forcing/TemplateForcing.vio
forcing/GRTT_SProp.vo forcing/GRTT_SProp.glob forcing/GRTT_SProp.v.beautified: forcing/GRTT_SProp.v forcing/TemplateForcing.vo forcing/translation_utils.vo
forcing/GRTT_SProp.vio: forcing/GRTT_SProp.v forcing/TemplateForcing.vio forcing/translation_utils.vio
